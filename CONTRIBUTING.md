# Contributing

Thanks for contributing to `OperatorEstimates`.

## Before opening a pull request

- open an issue or discussion for changes to the public theorem surface
- keep the public contract narrow and typed
- run `lake update`
- run `lake build`
- do not introduce `sorry` or `admit`
- update public docs when the public contract or theorem surface changes

## Contribution style

- prefer explicit hypotheses over narrative justification
- keep new modules within the stated bounded-operator scope
- do not broaden the public surface implicitly through examples or drafts
