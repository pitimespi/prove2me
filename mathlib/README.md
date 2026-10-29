# Missions that use Mathlib

The missions in this directory state claims about the system rather than the rules (selfish mining,
the replacement rules, the backbone properties) and use Mathlib (ℝ, series, `ring`, `linarith`). They
are built in their own Lake project pinned to the platform's Mathlib commit (`lakefile.lean` here):

```
cd mathlib && lake update && lake exe cache get && lake build
```

The consensus definitions they refer to (`Definitions/Def_Bitcoin*.lean` of the main project) import only
`Std` and are copied into this project's `Definitions/` at build time (`cp ../Definitions/Def_Bitcoin*.lean Definitions/`).
Each `NOTES_<NS>.md` states the model, the hypotheses, the literature it follows, and what is not proved.
