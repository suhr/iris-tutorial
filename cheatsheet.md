# Connectives

| Name                    | Notation     | Introduction                      | Elemination    |
| ----------------------- | ------------ | --------------------------------- | -------------- |
| `BI.and`                | `P ∧ Q`      | `isplit`                          |                |
| `BI.or`                 | `P ∨ Q`      | `ileft`, `iright`                 | `(HP \| HQ)`   |
| `BI.sep`                | `P ∗ Q`      | `isplitl`, `isplitr`              | `⟨HP, HQ⟩`     |
| `BI.wand`               | `P -∗ Q`     | `iintro`                          | `iapply`       |
| `BI.pure`               | `⌜ ϕ ⌝`      | `!%`, `ipureintro`, `imodintro`   | `%ϕ`           |
| `BI.exists`             | `∃ x : A, P` | `iexists`                         | `⟨%x, HP⟩`     |
| `BI.forall`             | `∀ x : A, P` | `%x`                              | `iapply`       |
| `BI.intuitionistically` | `□ P`        | `!>`, `imodintro`                 | `#HP`          |
| `BI.later`              | `▷ P`        | `!>`, `inext`, `imodintro`        | `>HP`          |
