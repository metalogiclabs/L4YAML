#!/usr/bin/env python3
"""Source census, not a Lean parser or semantic completeness certificate.
Pins every grammar file and scanner state layout; closure intentionally fails
until a separately audited full-language theorem consumer is implemented.
"""
import argparse, copy, hashlib, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
MAP = ROOT / 'research/whole-source/source-bridge-map.json'

def uncomment(s):
    # Preserve line numbers; nested Lean comments and quoted literals are handled.
    out=[]; i=0; depth=0; quote=False
    while i < len(s):
        pair=s[i:i+2]; c=s[i]
        if depth:
            if pair=='/-': depth+=1; out.extend('  '); i+=2; continue
            if pair=='-/': depth-=1; out.extend('  '); i+=2; continue
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if quote:
            out.append(c)
            if c=='\\' and i+1<len(s): out.append(s[i+1]); i+=2; continue
            if c=='"': quote=False
            i+=1; continue
        if c=='"': quote=True; out.append(c); i+=1; continue
        # Lean character literals can contain a quote or comment punctuation.
        char=re.match(r"'(?:\\.|[^'\\\n])'",s[i:]) if c=="'" else None
        if char: out.append(char[0]); i+=len(char[0]); continue
        if pair=='/-': depth=1; out.extend('  '); i+=2; continue
        if pair=='--':
            j=s.find('\n',i); j=len(s) if j<0 else j
            out.append(' '*(j-i)); i=j; continue
        out.append(c); i+=1
    if depth or quote: raise ValueError('unterminated comment/string')
    return ''.join(out)

def census():
    result={}
    for p in sorted((ROOT/'L4YAML/Surface').glob('*.lean')):
        raw=p.read_text(); lines=uncomment(raw).splitlines(); decls={}; active=None; base=0
        for line in lines:
            d=re.match(r'^(\s*)(inductive|structure|def|abbrev|lemma|theorem)\s+(\w+)',line)
            if d:
                active=None
                if d[2] in ('inductive','structure','def','abbrev'):
                    active=d[3]; base=len(d[1]); decls[active]={'kind':d[2],'constructors':[]}
                continue
            c=re.match(r'^(\s*)\|\s+(\w+)\b',line)
            if c and active and decls[active]['kind']=='inductive' and len(c[1])>base:
                decls[active]['constructors'].append(c[2])
        result[str(p.relative_to(ROOT))]={'sha256':hashlib.sha256(raw.encode()).hexdigest(),'declarations':decls}
    p=ROOT/'L4YAML/Scanner/State.lean'; raw=p.read_text(); clean=uncomment(raw)
    state=clean.split('structure ScannerState where',1)[1].split('deriving',1)[0]
    result[str(p.relative_to(ROOT))]={'sha256':hashlib.sha256(raw.encode()).hexdigest(),'fields':re.findall(r'^  (\w+)\s*:',state,re.M)}
    return result

def check_requirements(m, normative_source=None):
    """Validate map integrity only; never certify semantic adequacy."""
    r=m['requirement_map']; index=r['production_index']; groups=r['groups']
    if [x['number'] for x in index] != list(range(1,212)):
        raise ValueError('normative production index must contain exactly 1..211')
    ids=[g['id'] for g in groups]
    if len(ids)!=len(set(ids)): raise ValueError('duplicate requirement family')
    assigned=[n for g in groups for n in g['productions']]
    if sorted(assigned)!=list(range(1,212)): raise ValueError('missing/duplicate production ownership')
    for x in index:
        if not any(g['id']==x['requirement_group'] and x['number'] in g['productions'] for g in groups):
            raise ValueError('production/family mapping mismatch')
    for path,digest in r['source_hashes'].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=digest:
            raise ValueError('requirement source drift: '+path)
    for g in groups:
        if g['action'] not in r['classification_meaning']: raise ValueError('unknown audit action')
        for ref in g['definition_candidates']:
            path,_,decl=ref.partition(':'); raw=(ROOT/path).read_text()
            if decl and not re.search(r'\b(?:def|abbrev|inductive|structure|lemma|theorem)\s+'+re.escape(decl)+r'\b',raw):
                raise ValueError('missing definition candidate: '+ref)
    if normative_source:
        raw=Path(normative_source).read_bytes(); pin=r['normative_source']
        if hashlib.sha256(raw).hexdigest()!=pin['sha256']: raise ValueError('normative source SHA256 mismatch')
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if blob!=pin['git_blob']: raise ValueError('normative source Git blob mismatch')
        names=[x.split('::=')[0].strip() for x in re.findall(r'^\[#\]\s+([^\n]+)',raw.decode(),re.M)]
        if names!=[x['name'] for x in index]: raise ValueError('normative production names mismatch')
    return len(index),len(groups),len(r['cross_cutting'])

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--record',action='store_true'); ap.add_argument('--closure',action='store_true'); ap.add_argument('--normative-source'); ap.add_argument('--self-test',action='store_true'); args=ap.parse_args()
    m=json.loads(MAP.read_text()); actual=census()
    if args.record:
        m['source_census']=actual; MAP.write_text(json.dumps(m,indent=2)+'\n')
    if m.get('source_census')!=actual:
        print('SOURCE CENSUS DRIFT: review source changes and regenerate explicitly'); return 1
    for path,row in actual.items():
        ds=row.get('declarations',{}); print(path, 'inductives=',sum(d['kind']=='inductive' for d in ds.values()),'constructors=',sum(len(d['constructors']) for d in ds.values()),'state_fields=',len(row.get('fields',[])))
    print('Census matches pinned source. This does not establish normative YAML coverage.')
    if 'requirement_map' in m:
        counts=check_requirements(m,args.normative_source)
        print('Requirement map integrity:',counts,'(productions, families, cross-cutting). Semantic adequacy UNKNOWN.')
        if args.self_test:
            mutations={
                'omission': lambda x: x['requirement_map']['production_index'].pop(),
                'misroute': lambda x: x['requirement_map']['production_index'][0].update(requirement_group='stream'),
                'source_drift': lambda x: x['requirement_map']['source_hashes'].update({'L4YAML/Surface/Basic.lean':'bad'})}
            for label,mutate in mutations.items():
                altered=copy.deepcopy(m); mutate(altered)
                try: check_requirements(altered)
                except ValueError: print('Negative control rejected:',label)
                else: raise ValueError('negative control admitted: '+label)

    if args.closure:
        print('CAPSTONE UNKNOWN: no qualified full independent language, full producer, same-language strictness, or full changed-source regression consumer.')
        print('The original converse is refuted. No metadata flag can promote this gate.')
        return 2
    return 0
if __name__=='__main__': raise SystemExit(main())
