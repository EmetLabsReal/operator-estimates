import Lake
open Lake DSL

package «operator-estimates» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6921b4054192c187cc03d6bcbfbcc1115000b99a"

@[default_target]
lean_lib «OperatorEstimates» where
  -- Build the public root plus the documented example module, without sweeping
  -- in unrelated draft files that happen to live under the same namespace.
  globs := #[
    `OperatorEstimates,
    `OperatorEstimates.Core.StrictDirichletPrelude,
    `OperatorEstimates.Core.StrictGenerator,
    `OperatorEstimates.Core.StrictResolvent,
    `OperatorEstimates.Core.StrictYosidaSemigroup,
    `OperatorEstimates.Examples.FuchsianQuotient,
    `OperatorEstimates.Examples.FischerProjection,
    `OperatorEstimates.Examples.ToyInstantiation,
    `OperatorEstimates.Examples.ThresholdCrossing,
    `OperatorEstimates.Examples.Regimes
  ]
