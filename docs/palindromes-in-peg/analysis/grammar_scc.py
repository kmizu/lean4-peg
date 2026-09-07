"""Well-formedness style analysis of a huge plain PEG.
Pass A: parse each rule body into prefix bytecode (ints).  Pass B: greatest fixpoint of
C = { rules that consume >= 1 char whenever they succeed }.  Pass C: tag every reference
edge as 'guarded' iff some element earlier in its enclosing sequence must consume; then
test the graph of UNGUARDED edges (reachable from S) for a cycle."""
import re, sys, array, time
path = sys.argv[1]; t0 = time.time()
TOK = re.compile(rb'"(?:[^"\\]|\\.)*"|\[(?:[^\]\\]|\\.)*\]|[A-Za-z_][A-Za-z0-9_]*|[()/&!*+?.]')
# opcodes
LIT, EMPTY, REF, STAR, PLUS, OPT, AND, NOT, SEQ, ALT = range(10)
ids = {}; names = []
with open(path, 'rb') as f:
    for line in f:
        if b' = ' not in line: continue
        nm = line.split(b' = ', 1)[0].strip()
        if nm not in ids: ids[nm] = len(names); names.append(nm)
n = len(names); print('rules', n, f'{time.time()-t0:.0f}s', flush=True)
code = array.array('i'); start = array.array('i', [0]) * (n + 1)

def parse(tokens):
    """prefix bytecode: op [arg]; SEQ/ALT are binary: SEQ a b"""
    out = []; pos = [0]
    def peek(): return tokens[pos[0]] if pos[0] < len(tokens) else None
    def take(): t = tokens[pos[0]]; pos[0] += 1; return t
    def primary():
        t = take()
        if t == b'(':
            e = choice(); assert take() == b')'; return e
        if t == b'&': return [AND] + primary_suffixed()
        if t == b'!': return [NOT] + primary_suffixed()
        if t == b'.': return [LIT]
        if t[:1] == b'"': return [EMPTY] if t == b'""' else [LIT]
        if t[:1] == b'[': return [LIT]
        return [REF, ids[t]]
    def primary_suffixed():
        e = primary()
        while peek() in (b'*', b'+', b'?'):
            s = take(); e = [{b'*': STAR, b'+': PLUS, b'?': OPT}[s]] + e
        return e
    def seq():
        e = primary_suffixed()
        while peek() not in (None, b'/', b')'):
            e = [SEQ] + e + primary_suffixed()
        return e
    def choice():
        e = seq()
        while peek() == b'/':
            take(); e = [ALT] + e + seq()
        return e
    e = choice(); assert pos[0] == len(tokens), tokens[pos[0]:pos[0]+3]
    return e

with open(path, 'rb') as f:
    i = 0
    for line in f:
        if b' = ' not in line: continue
        nm, body = line.split(b' = ', 1)
        toks = TOK.findall(body.rstrip(b';\r\n '))
        start[i] = len(code); code.extend(parse(toks)); i += 1
start[n] = len(code); print('bytecode ints', len(code), f'{time.time()-t0:.0f}s', flush=True)

def mc_eval(lo, hi, C):
    """must-consume of prefix bytecode code[lo:hi] under set C (bytearray)."""
    st = []; k = lo
    # evaluate prefix code right-to-left with a stack
    k = hi - 1
    while k >= lo:
        op = code[k]
        if op == REF: pass  # handled below (arg precedes? no: [REF, id] -> id at k, REF at k-1)
        k -= 1
    # simpler: recursive descent over prefix code
    def ev(k):
        op = code[k]
        if op == LIT: return True, k + 1
        if op == EMPTY: return False, k + 1
        if op == REF: return bool(C[code[k + 1]]), k + 2
        if op in (STAR, OPT, AND, NOT): _, k2 = ev(k + 1); return False, k2
        if op == PLUS: return ev(k + 1)
        if op == SEQ:
            a, k2 = ev(k + 1); b, k3 = ev(k2); return (a or b), k3
        if op == ALT:
            a, k2 = ev(k + 1); b, k3 = ev(k2); return (a and b), k3
        raise ValueError(op)
    v, _ = ev(lo); return v

sys.setrecursionlimit(100000)

# reverse dependencies: for each rule, which rules reference it
rsrc = array.array('i'); rdst = array.array('i')
for r in range(n):
    k = start[r]; hi = start[r + 1]
    while k < hi:
        op = code[k]
        if op == REF: rsrc.append(code[k + 1]); rdst.append(r); k += 2
        else: k += 1
RE = len(rsrc); rdeg = array.array('i', [0]) * (n + 1)
for s_ in rsrc: rdeg[s_ + 1] += 1
for i in range(n): rdeg[i + 1] += rdeg[i]
rpos = array.array('i', rdeg[:n]); radj = array.array('i', [0]) * RE
for k in range(RE):
    p = rpos[rsrc[k]]; radj[p] = rdst[k]; rpos[rsrc[k]] = p + 1
del rsrc, rdst
print('reverse edges', RE, f'{time.time()-t0:.0f}s', flush=True)
C = bytearray([1]) * n
queued = bytearray([1]) * n; work = list(range(n))
flips = 0; evals = 0
while work:
    r = work.pop(); queued[r] = 0; evals += 1
    if C[r] and not mc_eval(start[r], start[r + 1], C):
        C[r] = 0; flips += 1
        for i in range(rdeg[r], rdeg[r + 1]):
            u = radj[i]
            if C[u] and not queued[u]: queued[u] = 1; work.append(u)
print(f'worklist gfp: evals {evals}, flips {flips}, consuming rules {sum(C)}', f'{time.time()-t0:.0f}s', flush=True)
# Pass C': full graph with per-edge consumption guard; SCCs; consuming edges inside SCCs
esrc = array.array('i'); edst = array.array('i'); eg = array.array('b')
def walk(k, pre, r):
    op = code[k]
    if op == LIT: return True, k + 1
    if op == EMPTY: return False, k + 1
    if op == REF:
        d = code[k + 1]; esrc.append(r); edst.append(d); eg.append(1 if pre else 0)
        return bool(C[d]), k + 2
    if op in (STAR, OPT, AND, NOT): _, k2 = walk(k + 1, pre, r); return False, k2
    if op == PLUS: return walk(k + 1, pre, r)
    if op == SEQ:
        a, k2 = walk(k + 1, pre, r); b, k3 = walk(k2, pre or a, r); return (a or b), k3
    if op == ALT:
        a, k2 = walk(k + 1, pre, r); b, k3 = walk(k2, pre, r); return (a and b), k3
for r in range(n): walk(start[r], False, r)
E = len(esrc); print(f'edges {E}, guarded by consumption {sum(eg)}', f'{time.time()-t0:.0f}s', flush=True)
deg = array.array('i', [0]) * (n + 1)
for s_ in esrc: deg[s_ + 1] += 1
for i in range(n): deg[i + 1] += deg[i]
pos = array.array('i', deg[:n]); adj = array.array('i', [0]) * E; adjg = array.array('b', [0]) * E
for k in range(E):
    p = pos[esrc[k]]; adj[p] = edst[k]; adjg[p] = eg[k]; pos[esrc[k]] = p + 1
del esrc, edst, eg
# iterative Tarjan restricted to nodes reachable from S
S = ids[b'S']
index = array.array('i', [-1]) * n; low = array.array('i', [0]) * n; onst = bytearray(n)
comp = array.array('i', [-1]) * n; st = []; idx = 0; ncomp = 0; compsize = []
work = [(S, deg[S])]; index[S] = low[S] = idx; idx += 1; st.append(S); onst[S] = 1
while work:
    v, i = work[-1]
    if i < deg[v + 1]:
        work[-1] = (v, i + 1); w = adj[i]
        if index[w] == -1:
            index[w] = low[w] = idx; idx += 1; st.append(w); onst[w] = 1; work.append((w, deg[w]))
        elif onst[w]:
            if index[w] < low[v]: low[v] = index[w]
    else:
        work.pop()
        if work:
            u = work[-1][0]
            if low[v] < low[u]: low[u] = low[v]
        if low[v] == index[v]:
            size = 0
            while True:
                w = st.pop(); onst[w] = 0; comp[w] = ncomp; size += 1
                if w == v: break
            compsize.append(size); ncomp += 1
reach = idx
intra_g = intra_u = 0; nontrivial = sum(1 for s_ in compsize if s_ > 1)
for v in range(n):
    if index[v] == -1: continue
    for i in range(deg[v], deg[v + 1]):
        w = adj[i]
        if comp[w] == comp[v]:
            if adjg[i]: intra_g += 1
            else: intra_u += 1
print(f'reachable from S: {reach} rules; SCCs: {ncomp}, nontrivial (size>1): {nontrivial}, largest: {max(compsize)}', flush=True)
print(f'edges inside SCCs: consuming-guarded {intra_g}, unguarded {intra_u}', f'{time.time()-t0:.0f}s', flush=True)
big = max(range(ncomp), key=lambda c: compsize[c])
print('sample rules of the largest SCC:', [names[v].decode() for v in range(n) if comp[v] == big][:6])
