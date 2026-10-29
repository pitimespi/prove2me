The size test fails and the `OP_ELSE` branch executes: `OP_DROP <expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP` through `cltv_step`, then `OP_CHECKSIG` on the remote key.
