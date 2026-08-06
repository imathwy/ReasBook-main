# Smooth Minimization of Non-Smooth Functions

- **Author:** Yurii Nesterov
- **Venue:** Mathematical Programming, Ser. A 103, 127–152 (2005), DOI: 10.1007/s10107-004-0552-5
- **Paper ID:** `SmoothMinimization_Nesterov_2004`
- **Branch/toolchain:** `v4.30.0` / `leanprover/lean4:v4.30.0`

## Contributors

- Wanli Ma (@wl-ma)
- Zichen Wang

## Coverage

Formalization of the paper's results on smooth minimization of non-smooth functions:
smoothing techniques and complexity guarantees for first-order methods.

## Statistics

- **Declarations:** 353 (theorem/lemma/example: 303; other: 50)
- **Lean code:** 27 `.lean` files, 15255 lines
- **Proof completion:** 353/353 (approx)
- **Remaining placeholders:** `sorry`: 0; `admit`: 0

## Build

```bash
cd ReasBook
lake build Papers.SmoothMinimization_Nesterov_2004.Paper
```

- Links: [Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/) | [Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Paper.html) | [Lean source](./Sections/)

## Sections

- Section 1: Introduction ([Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/sections/section01/)) ([Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section01.html)) ([Lean source](./Sections/))
- Section 2: Smooth Approximations of Non-differentiable Functions ([Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/sections/section02/)) ([Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section02.html)) ([Lean source](./Sections/))
- Section 3: Fast Gradient Methods ([Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/sections/section03/)) ([Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section03.html)) ([Lean source](./Sections/))
- Section 4: Applications ([Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/sections/section04/)) ([Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section04.html)) ([Lean source](./Sections/))
- Section 5: Implementation Issues and Modifications ([Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/sections/section05/)) ([Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section05.html)) ([Lean source](./Sections/))
