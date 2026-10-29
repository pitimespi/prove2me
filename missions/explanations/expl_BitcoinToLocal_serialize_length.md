`natBytes n` has at most $k$ bytes when $n < 256^k$ (induction on $k$); `serialize` adds at most one sign byte (or sets the top bit in place, preserving the length).
