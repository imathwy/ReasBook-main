import StacksProject_2024.Chap15.Definition_15_125_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- 
Domain-style sampling:
- primary domain: Smith normal form over domains and the induced Bézout property of finitely
  generated ideals;
- sampled owner API:
  `Matrix.HasElementaryDivisorDiagonal`,
  `IsElementaryDivisorDomain`,
  `IsBezout`,
  `isBezout_of_isElementaryDivisorDomain`;
- best owner abstraction: the chapter owner for the source hypothesis is
  `IsElementaryDivisorDomain`, introduced in `Definition_15_125_5`, and the target conclusion is
  the canonical mathlib owner `IsBezout`;
- primitive vs. derived:
  the Smith-normal-form diagonalization data are primitive source-facing content already owned by
  `Definition_15_125_5`, while the Bézout-domain conclusion is derived API owned by the instance
  `isBezout_of_isElementaryDivisorDomain`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma asserting that every elementary divisor domain is Bézout;
  `core/canonical`: `IsElementaryDivisorDomain` and `IsBezout`;
  `bridge/view`: this file, which should reuse the upstream owner instance directly rather than
  duplicate the Smith-normal-form data and reprove the implication locally.

The previous local file rebuilt `smithDiagonal`, the diagonal-chain predicate, the elementary
divisor domain class, and the PID instance. Those are redundant primitive owners once
`Definition_15_125_5` exists, so the canonical refinement is direct recall of the upstream
instance.
-/

/- Lemma 15.125.6: every elementary divisor domain is a Bézout domain. This is exactly the
chapter instance `isBezout_of_isElementaryDivisorDomain`. -/
#check isBezout_of_isElementaryDivisorDomain
