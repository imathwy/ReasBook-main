import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.3 is `bridge/view`: Definition 6.7 already owns the Moreau envelope `M[μ, f]`, Chapter 2
already owns `infimal_convolution` together with the textbook notation `□`, and Definition 6.7
also owns the quadratic kernel `ω_μ`. The source only recalls that `M_f^μ` is the infimal
convolution of `f` with `ω_μ`, so the canonical owner declarations are reused directly here
instead of keeping a duplicate theorem wrapper. -/

recall infimal_convolution
recall moreau_quadratic_kernel
recall moreau_envelope
