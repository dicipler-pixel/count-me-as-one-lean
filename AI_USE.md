# AI use

The research direction and the three working rules this repository serves are Jeromie Beasley's.
The Lean code, the false controls and the verification harness were written with Claude (Anthropic).
Every theorem is checked by the Lean kernel, replayed in `leanchecker`, and axiom-audited by
`scripts/verify.py`. Nothing here relies on trusting the AI: the checks either pass or fail.
