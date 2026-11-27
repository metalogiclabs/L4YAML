import json, pathlib, sys, hashlib
spec=json.loads(pathlib.Path(sys.argv[1]).read_text())
phase=sys.argv[2]
p=pathlib.Path(spec["path"])
s=p.read_text()
for e in spec["common"]+spec[phase]:
    assert s.count(e["old"])==1, e["label"]
    s=s.replace(e["old"],e["new"],1)
p.write_text(s)
print(phase, len(spec["common"]+spec[phase]), hashlib.sha256(p.read_bytes()).hexdigest())
