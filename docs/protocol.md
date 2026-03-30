# Public Protocol

This stack is evaluated by one question:

**Can we throw away this sector and does the remaining sector still control its own boundary?**

This protocol turns that question into a fixed read path and a fixed reporting standard.

## Read Path

1. `operator-estimates/docs/contract.md`
2. `QuantOE/docs/exact-license-spec.md`
3. `stochastic-admissibility/README.md`

That order fixes the forcing order:

1. exact license or exact obstruction
2. bounded `chi` license on the forced carrier
3. concrete stochastic/process/boundary theorem space on that same carrier

## Reporting Standard

Any public reduction claim should report:

- the retained sector `P`
- the omitted sector `Q`
- exact-tier status
- exact-tier schema version
- `gamma`
- `lambda`
- `chi`
- resulting regime

In `QuantOE`, that exact-tier surface is the frozen `exact_license` schema:

- `schema_version = "v1"`
- `status`
- `reason_code`
- `invariant_kind`
- `provenance`
- `conserved_quantities`
- `exact_defects`

If the exact tier is not supplied, the report must say so explicitly:

- `exact_license.status = external`
- `exact_license.reason_code = external_certificate_required`

## Submission Rule

The stack certifies reported cuts. It does not search them.

So any serious comparison against this stack must present:

- the proposed partition
- the exact-tier certificate or obstruction record
- the bounded-tier report for that same cut

No variance score, reconstruction score, or domain narrative substitutes for that protocol.

## Public Challenge Display

Proof layer:

```bash
cd operator-estimates
lake build
```

Numeric layer:

```bash
cd QuantOE
cargo test --locked
PYTHONPATH=python python3 scripts/run_public_challenge_suite.py
```

Concrete theorem layer:

```bash
cd stochastic-admissibility
lake build
lake build StochasticAdmissibility.Examples.LicensedDecompositionChain
```

The public challenge suite in `QuantOE` displays:

- pre-admissible witness
- supercritical witness
- subcritical witness
- exact-tier subcritical witness

## Scope Boundary

What remains external:

- Grassmannian search / partition orchestration
- application-specific rigidity discharge
- domain semantics beyond the supplied certificate and cut

What is internal and frozen:

- exact forcing order
- bounded `chi` license
- public exact-tier certificate schema
- the stochastic theorem spine on licensed cuts
