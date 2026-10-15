import Counting.Algorithm.Affine.Clients

open Counting.Algorithm.Affine Counting.Algorithm.Affine.Clients
open Holant.Tractable

#eval decide (program (AffineSystem.unconstrained 1) (unary 0) = unaryCode 0)
#eval decide (program (AffineSystem.unconstrained 1) (unary 1) = unaryCode 1)
#eval decide (program (AffineSystem.unconstrained 1) (unary 2) = .zero)
#eval decide (program (AffineSystem.unconstrained 1) (unary 3) = unaryCode 3)
#eval decide (program (badSupport 3) (QuadraticPhase.zero 3) = .zero)
#eval decide (program (AffineSystem.unconstrained 2) pairPhase = unaryCode 0)
#eval transitions (AffineSystem.unconstrained 2) pairPhase
#eval (program (AffineSystem.unconstrained 2) pairPhase).code.length
