We prove that the next required target, once decoded, is at most $\mathrm{powLimit} = 2^{224} - 1$, for every last word and all block times.

`CalculateNextWorkRequired` ends with a cap: the value it re-encodes is $\min(x, \mathrm{powLimit})$ for some $x$, hence at most $\mathrm{powLimit}$, which is below $2^{256}$. By `BitcoinPow.getCompact_le` the decoded re-encoding is at most that value, hence at most $\mathrm{powLimit}$. No hypothesis on the last word is needed, since the cap applies whatever the earlier arithmetic produced.
