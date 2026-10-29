`getOp` on a non-push byte consumes exactly one byte, so the suffix recorded for an opcode is the script after its position; the position is the length of the consumed prefix (`annotate_suffix`).
