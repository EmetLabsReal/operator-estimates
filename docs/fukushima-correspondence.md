# Fukushima Correspondence

The exact layer beneath the bounded admissibility contract is form descent.

Fix a full carrier with an energy form `E`. Suppose a group action preserves that form exactly on an
invariant domain. The question is then not yet whether a bounded Schur reduction is licensed. The
prior question is whether the proposed quotient is licensed at all.

The quotient is licensed when the energy form survives the identification as a closed descended
form. This is the Fukushima correspondence in the present stack:

- full object: the original closed semibounded form
- retained object: the quotient carrier
- exact invariant: pullback of the descended quotient form recovers the original energy
- failure boundary: accumulation destroys proper discontinuity, so no exact descended form is
  licensed on the proposed quotient

This is an exact theorem layer. It does not use `chi`.

On the actual quotient carrier, the public theorem surface goes further: exact pullback fixes the
descended Markov energy uniquely. Above that exact carrier, the public theorem surface places the
quotient-side generator, realized effective semigroup, Hunt realization, and the boundary
capacity/trace package on the forced quotient and keeps them in scope only there.

The public example is
`OperatorEstimates/Examples/FuchsianQuotient.lean`. The Fuchsian hypotheses are
packaged as explicit inputs rather than re-derived from the full hyperbolic geometry of
`PSL(2,R)` acting on the upper half-plane.

Once exact quotient licensing and actual-quotient Markov uniqueness are established, the bounded
layer sits above them:

- exact quotient licensing: the form survives descent
- actual-quotient Markov uniqueness: the descended energy and generator are
  fixed by exact pullback
- exact analytic/process layer: the public theorem surface places the quotient-side generator,
  realized effective semigroup, Hunt process, and boundary package on the forced carrier
- exact-to-bounded bridge: once that carrier is forced, the bounded Schur setup and cascade
  theorems are evaluated on it
- process/boundary bridge: the public Hunt and boundary layers are kept downstream of
  that same forced-carrier/cascade interface, both through the single-scale bridge objects and the
  hierarchy-indexed cascade bridge objects
- bounded reduction licensing: the retained/omitted split survives Schur return with
  `chi = (lambda / gamma)^2 < 1`

The lower layer decides whether the quotient is real and what dynamics are licensed on it. The
upper layer decides whether a bounded reduction across that forced carrier is licensed.

No descended form, no descended effective semigroup. No descended effective semigroup, no descended process. No
descended process, no Schur.
