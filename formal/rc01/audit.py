import re, pathlib
source=pathlib.Path("RC01Proof.lean").read_text()
log=pathlib.Path("lean-audit.log").read_text()
names=re.findall(r"^#print axioms (\w+)",source,re.M)
allowed={"propext","Classical.choice","Quot.sound"}
for n in names:
    m=re.search(r"'RC01\."+n+r"' depends on axioms: \[([^\]]*)\]",log,re.S)
    if m:
        deps={x.strip() for x in m.group(1).split(",") if x.strip()}
        assert deps<=allowed,(n,deps)
    else:
        assert re.search(r"'RC01\."+n+r"' does not depend on any axioms",log),n
assert len(names)==len(set(names))
assert "sorryAx" not in log
print(f"AXIOM AUDIT PASS: {len(names)} declarations")
