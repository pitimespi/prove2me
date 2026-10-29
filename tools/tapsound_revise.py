"""Revision 2 of the Taproot-soundness mission, in place on the changes-requested proposal:
deprecate the first-revision nodes with a note, delete their items from the proposal, create the
V2 definition item, then (finish_proposal.py) the V2 theorem items, order and goal."""
import json, pipeline
tok = pipeline.token()
P = json.load(open("tapsound_proposal.json")); pid = P["proposal_id"]
st, p = pipeline.call("GET", f"/mission-proposals/{pid}", None, tok)
old = {i["theorem_name"]: i for i in p["items"]}
print("status", p["status"], "items", len(old))
NOTE = ("\n\n**Deprecated.** Superseded by `{v2}` (revision 2, `BitcoinTapSoundnessV2`): this revision's "
        "collision alternatives were closed propositions (`Sha256Collision`, and `TweakCollision` without a "
        "length constraint), which are provable by counting and so made the statement trivially true; the V2 "
        "declarations name the colliding strings and the two 32-byte tweaks explicitly, computed from the inputs.")
for name, it in old.items():
    if not name.startswith("BitcoinTapSoundness."): 
        if name != "BitcoinTapSoundness": continue
    v2 = name.replace("BitcoinTapSoundness", "BitcoinTapSoundnessV2", 1)
    if it.get("theorem_id"):
        body = {"deprecated": True, "natural_language_statement": (it.get("natural_language_statement") or "") + NOTE.format(v2=v2)}
        st, r = pipeline.call("PATCH", f"/theorems/{it['theorem_id']}", body, tok)
        print("deprecate", name, st, (str(r) if st != 200 else "")[:200])
    st, r = pipeline.call("DELETE", f"/mission-proposals/{pid}/items/{it['id']}", None, tok)
    print("delete item", name, st)
# the one item deleted earlier in the API test (tapleaf_ne_tapbranch) still needs deprecating
tid = P["items"].get("BitcoinTapSoundness.tapleaf_ne_tapbranch")
if tid and "BitcoinTapSoundness.tapleaf_ne_tapbranch" not in old:
    st, t = pipeline.call("GET", f"/theorems/{tid}", None, tok)
    body = {"deprecated": True, "natural_language_statement": (t.get("natural_language_statement") or "") + NOTE.format(v2="BitcoinTapSoundnessV2.tapleaf_ne_tapbranch")}
    st, r = pipeline.call("PATCH", f"/theorems/{tid}", body, tok)
    print("deprecate tapleaf_ne_tapbranch", st, (str(r) if st != 200 else "")[:200])
# V2 definition item
import importlib.util, pathlib
M = __import__("tapsound2_items")
code = pathlib.Path("/root/prove2me_workspace/Definitions/Def_BitcoinTapSoundnessV2.lean").read_text()
D = M.DEFINITION
st, r = pipeline.call("POST", f"/mission-proposals/{pid}/items", {"kind": "definition", "definition_name": D["definition_name"],
    "definition_title": D["definition_title"], "definition": code, "natural_language_statement": D["natural_language_statement"],
    "source": M.SRC, "tags": M.TAGS}, tok)
print("def item", st, (str(r) if st not in (200, 201) else r["id"])[:300])
desc = pathlib.Path("tapsound2_description.md").read_text()
st, r = pipeline.call("PATCH", f"/mission-proposals/{pid}", {"description": desc}, tok)
print("description", st, (str(r) if st != 200 else "")[:200])
