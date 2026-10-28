"""Post-publication swap for the BitcoinBlock -> BitcoinBlockV2 revision.

Usage: python3 blockv2_swap.py [--dry]
  1. reads the published BitcoinBlockV2 proposal and maps names -> theorem ids
  2. deprecates the 20 original BitcoinBlock nodes with a note naming the replacement
  3. on the umbrella proposal, replaces each old BitcoinBlock reference with the V2 one
     (same position in item_order) and moves main_item_id to BitcoinBlockV2.acceptance
"""
import json, sys, pipeline
DRY = "--dry" in sys.argv
UMB = "c416e514-a450-41cc-8dd7-bef33d605a8e"
OLD = json.load(open("blk_proposal.json"))["proposal_id"]
NEW = json.load(open("blk2v_proposal.json"))["proposal_id"]
tok = pipeline.token()

st, newp = pipeline.call("GET", f"/mission-proposals/{NEW}", None, tok)
assert st == 200, newp
print("new proposal status:", newp["status"])
new_ids = {i["theorem_name"]: i["theorem_id"] for i in newp["items"] if i.get("theorem_id")}
if len(new_ids) < 20:
    sys.exit(f"only {len(new_ids)} V2 items have theorem ids; publish the revision first")

st, oldp = pipeline.call("GET", f"/mission-proposals/{OLD}", None, tok)
old = {i["theorem_name"]: i for i in oldp["items"]}

# 1. deprecate old nodes
for name, it in old.items():
    v2 = name.replace("BitcoinBlock", "BitcoinBlockV2", 1)
    assert v2 in new_ids, v2
    note = (f"\n\n**Deprecated.** Superseded by `{v2}` (revision 2 of the block mission): the "
            f"`p2shSigOpCount` of this revision counted every push of `scriptSig` instead of only the "
            f"redeem script, over-counting P2SH sigops; the V2 declarations carry the corrected definition.")
    body = {"deprecated": True, "natural_language_statement": (it["natural_language_statement"] or "") + note}
    if DRY: print("would deprecate", name, it["theorem_id"]); continue
    st, r = pipeline.call("PATCH", f"/theorems/{it['theorem_id']}", body, tok)
    print("deprecate", name, st, (r if st != 200 else "")[:200])

# 2. umbrella swap
st, u = pipeline.call("GET", f"/mission-proposals/{UMB}", None, tok)
json.dump(u, open("umbrella_backup_before_v2_swap.json", "w"))
order = [i["id"] for i in u["items"]]
old_refs = {i["theorem_name"]: i for i in u["items"] if (i.get("theorem_name") or "").startswith("BitcoinBlock.") or i.get("theorem_name") == "BitcoinBlock"}
new_items = {}
for name, ref in old_refs.items():
    v2 = name.replace("BitcoinBlock", "BitcoinBlockV2", 1)
    if DRY: print("would replace", ref["id"], name, "->", v2, new_ids[v2]); continue
    st, r = pipeline.call("POST", f"/mission-proposals/{UMB}/items", {"kind": "reference", "theorem_id": new_ids[v2]}, tok)
    assert st in (200, 201), (st, r)
    new_items[name] = r["id"]
    order[order.index(ref["id"])] = r["id"]
    st, r = pipeline.call("DELETE", f"/mission-proposals/{UMB}/items/{ref['id']}", None, tok)
    print("swap", name, "add ok, delete", st)
if not DRY:
    st, r = pipeline.call("PATCH", f"/mission-proposals/{UMB}", {"item_order": order, "main_item_id": new_items["BitcoinBlock.acceptance"]}, tok)
    print("umbrella order/main", st, (r if st != 200 else "")[:300])
    st, u = pipeline.call("GET", f"/mission-proposals/{UMB}", None, tok)
    names = [i.get("theorem_name") for i in u["items"]]
    print("umbrella items", len(u["items"]), "V2 refs", sum(1 for n in names if (n or "").startswith("BitcoinBlockV2")),
          "old refs left", sum(1 for n in names if n == "BitcoinBlock" or (n or "").startswith("BitcoinBlock.")),
          "main is V2.acceptance", u["main_item_id"] == new_items["BitcoinBlock.acceptance"])
    json.dump(u, open("umbrella_current.json", "w"))
