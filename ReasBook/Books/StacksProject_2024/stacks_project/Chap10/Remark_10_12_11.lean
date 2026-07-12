import StacksProject_2024.Chap10.Example_10_12_12

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: exactness of linear maps under tensor product in commutative algebra;
- sampled owner declarations of the same kind:
  `LinearMap.exact_zero_iff_injective`,
  `Module.Flat.rTensor_exact`,
  `Module.Flat.iff_rTensor_exact`;
- layer:
  `source-facing`: the present counterexample is the explicit sequence `0 ⟶ ℤ ⟶ ℤ`;
  `core/canonical`: preservation of exact sequences under right tensoring is owned by
  `Module.Flat`;
  `bridge/view`: exactness of `0 ⟶ M ⟶ N` is canonically equivalent to injectivity of the second
  map via `LinearMap.exact_zero_iff_injective`;
- primitive data vs. derived API:
  primitive data: the explicit map `((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ)` and the tensor factor
  `ZMod 2`, provided by `Example_10_12_12`;
  derived API: exactness of the original sequence and failure of exactness after tensoring, both
  transported through the bridge theorem above. -/

/-- Remark 10.12.11: tensoring with an arbitrary module does not preserve exactness in general; the
exact sequence `0 ⟶ ℤ \xrightarrow{2} ℤ` becomes nonexact after tensoring with `ℤ/2ℤ`. -/
theorem tensorProduct_not_preserve_exact_sequence :
    Function.Exact (0 : Unit →ₗ[ℤ] ℤ) ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ∧
      ¬ Function.Exact ((0 : Unit →ₗ[ℤ] ℤ).rTensor (ZMod 2))
        (((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).rTensor (ZMod 2)) := by
  simpa [LinearMap.exact_zero_iff_injective] using
    tensoring_zmodTwo_does_not_preserve_injectivity
