# Instructions for a blind read-back of a mission

You are an independent auditor. You receive only Lean code: the mission's definitions file(s) and its theorem
statements (the `Theorems/Thm_<NS>_<name>.lean` stubs, whose proofs are `sorry` by design). You must NOT read the
mission's natural-language documentation (`missions/items/*`, `missions/descriptions/*`, `missions/explanations/*`,
`NOTES_*.md`, the `Solutions/` proofs): the point of a read-back is to state, from the code alone, what the
definitions are and what each theorem literally asserts, so that it can be compared afterwards with what the authors
claim. Docstrings inside the Lean files are part of the code you may read, but they are claims too: render what the
Lean term says, and if a docstring says something the term does not, point it out.

For the definitions file, write `readback_Def_<NS>.md`: every definition in order, rendered precisely in mathematics
and plain prose — its type, every case, every guard and its order, every default, what is left unconstrained.
Unfold enough that a reader who never sees the Lean can reconstruct its meaning. Where a definition transcribes source
code it cites (a Java method with line numbers), you may check the citation against the source if it is available
locally, and say whether the transcription matches.

For each theorem, write `readback_<NS>_<name>.md`:

1. **Declaration.** Every universally quantified variable with its type, every hypothesis (named, in order), and the
   conclusion, rendered precisely in mathematics and prose. Unfold the definitions it uses as far as needed to say
   what is actually claimed.
2. **What is not constrained.** Variables and fields the statement leaves free; hypotheses that make the statement
   weaker than it might look; whether any hypothesis could be unsatisfiable or make the statement vacuous (say so if
   you suspect it, with a reason).
3. **Plain-language summary**, two or three sentences, without overclaiming.

Be literal and exhaustive; do not speculate about intended meaning beyond the code; flag anything ambiguous,
surprising, vacuous-looking or inconsistent with the docstring.
