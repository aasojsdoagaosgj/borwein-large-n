# Root-phase dependency repair

The previous publication ZIP, SHA-256
`a7fe13b76389f5515210e59d0c093c5ffcd7ef2ab93caeff728118e4b88c977b`,
failed a fresh source rebuild after 59 successful modules. Its
`EndpointCombinedPhase` module referred to a coefficient definition and
two estimates that were absent from the supplied `EndpointPhaseSeries`.
That file instead defined the derivative series used elsewhere.

`EndpointRootPhaseSeries` now proves the required root-phase estimates in a
separate namespace. `EndpointCombinedPhase`, `EndpointCombinedTail`, and `EndpointStrongPhase`
explicitly use that namespace. The existing derivative-series file is
preserved. The consumer theorem statements, constants, and final threshold
are unchanged. The eight `MomentExponentChunk` proofs now share one
kernel-checked adjacent-pair certificate, avoiding repeated normalization of
large array lookups while preserving their public statements and all numerical
data. No proof placeholder or new
axiom was introduced.

The corrected source closure was then rebuilt from an empty output tree.
The final sign theorem, zero classification, and zero count all passed a
fresh axiom audit. See [clean-build.json](clean-build.json).
