import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_1

universe u v w

variable {ι : Type u} {Ω : Type v} {E : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace E]

/- Remark 9.2: this is a terminological recall of the chapter's owner abstraction for stochastic
processes with arbitrary index set. The primitive data is just a family `ι → Ω → E`, and the
separate random-variable condition is recorded by `IsStochasticProcess`. -/
recall IsStochasticProcess

/- Companion specification: `IsStochasticProcess X` means exactly that every coordinate `X i` is
measurable. -/
recall isStochasticProcess_iff
