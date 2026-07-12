import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: irreducibility criteria for binomials `X ^ p - C a` over a field;
* sampled owner declarations:
  `X_pow_sub_C_irreducible_of_prime`,
  `X_pow_sub_C_irreducible_iff_of_prime`,
  `pow_ne_of_irreducible_X_pow_sub_C`,
  `root_X_pow_sub_C_pow`;
* best owner abstraction: the mathlib theorem `X_pow_sub_C_irreducible_of_prime`;
* primitive data: a field `F`, a prime `p`, an element `a : F`, and the hypothesis that `a` is
  not a `p`th power;
* derived API: the irreducibility of `X ^ p - C a`.

Layer triage:
* `core/canonical`: this file is just the canonical irreducibility theorem for `X ^ p - C a`;
* `bridge/view`: the textbook wording adds a characteristic-`p` hypothesis, but that assumption is
  redundant for the actual owner theorem and should not survive as primitive public API.

So this item should be a direct recall of the owner theorem, not a parallel local wrapper with a
weaker proof route.
-/

/- Lemma 9.14.2: if `F` has characteristic `p` and `t` has no `p`th root in `F`, then
`X ^ p - C t` is irreducible over `F`. Mathlib proves the stronger canonical statement without the
characteristic-`p` assumption, namely `X_pow_sub_C_irreducible_of_prime`. -/
recall X_pow_sub_C_irreducible_of_prime
