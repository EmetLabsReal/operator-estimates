# OperatorEstimates

[![CI](https://github.com/EmetLabsReal/operator-estimates/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/EmetLabsReal/operator-estimates/actions/workflows/lean_action_ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Lean 4.29.0-rc6](https://img.shields.io/badge/Lean-4.29.0--rc6-blue)](lean-toolchain)

Lean proofs for licensed reduction.

Standard reduction starts by choosing a retained sector and only later asks whether the reduced
object behaves well. This library formalizes the prior question:

**Can we throw away this sector and does the remaining sector still control its own boundary?**

That question has two tiers.

- Exact tier: if the quotient or descended form is obstructed, the reduction is not in scope.
- Bounded tier: on an admitted split, `chi = (lambda / gamma)^2` decides the cut.

So:

- `chi < 1`: licensed
- `chi >= 1`: unlicensed

No descended form, no Schur question.

## Core Claim

The cut is the first nontrivial mathematical act.

What matters is not how much detail a reduction retains. What matters is whether the retained
sector remains responsible for the omitted return through the boundary. Variance explained,
reconstruction quality, and similar proxies do not license that cut.

## Read Path

- `docs/contract.md`
- `docs/protocol.md`
- `docs/admissibility-layers.md`
- `docs/fukushima-correspondence.md`

Witness modules:

- `OperatorEstimates/Examples/FuchsianQuotient.lean`
- `OperatorEstimates/Examples/Regimes.lean`
- `OperatorEstimates/Examples/ToyInstantiation.lean`

## Build

```bash
lake update
lake build
```

No `sorry`.

## Citation

If you use this library in research, cite `CITATION.cff`.

## License

MIT
