import Counting.ComplexCSP
import Counting.ComplexCSPClassification

/-! Complete ComplexCSP recognition and fixed-language classification.

The original encoded ordinary and degree recognizers decide which proved
tractability or charged-hardness branch applies. Exact algebraic descriptions,
positive arities and domain size, each supplied finite rational-basis realization,
and the positive degree modulus are retained. Evaluation uses the original
canonical-instance promise. Recognition is terminating on valid encoded input;
no uniform polynomial recognition bound or natural-valued #P membership follows.
-/
