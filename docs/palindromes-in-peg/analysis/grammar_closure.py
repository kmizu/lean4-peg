import re, sys
ident = re.compile(rb'[A-Za-z_][A-Za-z0-9_]*')
defined = set(); referenced = set(); nrules = 0
with open(sys.argv[1], 'rb') as f:
    for line in f:
        if b' = ' not in line: continue
        name, body = line.split(b' = ', 1)
        defined.add(name.strip()); nrules += 1
        # strip string literals and char classes so their contents are not taken as names
        body = re.sub(rb'"[^"]*"|\[[^\]]*\]', b' ', body)
        referenced.update(ident.findall(body))
missing = referenced - defined
unused = defined - referenced - {b'S'}
print(f'rules={nrules} defined={len(defined)} referenced={len(referenced)} MISSING={len(missing)} unused_defs={len(unused)}')
print('missing sample:', sorted(missing)[:10])
