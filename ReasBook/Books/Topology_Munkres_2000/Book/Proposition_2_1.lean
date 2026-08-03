module

import Mathlib.Logic.Function.Defs

/- Proposition 2.1 (1): A function is injective when equal outputs imply equal
inputs. -/
#check Function.Injective

/- Proposition 2.1 (2): A function is surjective when every element of its
specified codomain is the output of at least one input. -/
#check Function.Surjective

/- Proposition 2.1 (3): The composite of two injective functions is injective. -/
#check Function.Injective.comp

/- Proposition 2.1 (4): The composite of two surjective functions is surjective. -/
#check Function.Surjective.comp

/- Proposition 2.1 (5): The composite of two bijective functions is bijective. -/
#check Function.Bijective.comp
