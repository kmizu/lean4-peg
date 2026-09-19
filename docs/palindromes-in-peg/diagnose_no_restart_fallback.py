"""Reproduce a broken-chain fallback after disabling the source restart.

Run from any directory with Python 3. This instruments the Python source; it
is NOT a Lean packed-run reachability proof or a refutation of CycleOracleOn.
The source algorithm is unchanged on disk. The only execution change is
removing its broken-chain restart branch; head-position hooks observe it.
"""
import ast, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import scaffold_galil as g
source = Path(__file__).with_name("scaffold_galil.py").read_text()
positions = dict.fromkeys(("right", "left", "center", "walker", "verifier"), 0)
raw = []
seen = []
class Violation(Exception): pass

def movement(name, method, other=None):
    if method == "right": positions[name] += 1
    elif method == "left": positions[name] -= 1
    else: positions[name] = positions[other]

def fallback(mode, chain):
    if mode != "scan": return
    C, right = positions["center"], positions["right"]
    R = right-C-1
    enc = [v for a in raw for v in (2, a)] + [2]
    if R < 0 or C-R < 0 or right >= len(enc): return
    P = enc[C-R:C+R+1]
    win = enc[right:C-R-1:-1]
    if P != P[::-1] or len(win) != 2*R+2:
        raise RuntimeError(("instrumentation geometry mismatch", C, R, right))
    chosen = max(r for r in range((len(win)-1)//2+1) if win[:2*r+1] == win[:2*r+1][::-1])
    d=R+1-chosen
    seen.append((C,R,d,chain.mode))
    if R>4*d:
        print({"scope":"Python no-restart source execution; not a Lean reachability proof", "prefix":"".join("ab"[v] for v in raw), "centre":C, "radius":R, "move":d, "chain":chain.mode}, flush=True)
        raise Violation

class Instrument(ast.NodeTransformer):
    def visit_If(self, node):
        if ast.unparse(node.test) == "chain.mode == 'broken'":
            return ast.copy_location(ast.Pass(), node)
        return self.generic_visit(node)
    def visit_Expr(self, node):
        if not isinstance(node.value, ast.Call): return node
        call=node.value
        if not isinstance(call.func, ast.Attribute) or not isinstance(call.func.value, ast.Name): return node
        obj,method=call.func.value.id,call.func.attr
        if obj == "fpp" and method == "reset":
            return [ast.copy_location(ast.parse("fallback(mode, chain)").body[0], node),node]
        if obj in positions and method in ("right","left","copy_from"):
            other=call.args[0].id if method == "copy_from" and isinstance(call.args[0],ast.Name) else None
            extra=ast.parse(f"movement({obj!r}, {method!r}, {other!r})").body[0]
            return [node,ast.copy_location(extra,node)]
        return node

module=ast.parse(source)
function=next(n for n in module.body if isinstance(n,ast.FunctionDef) and n.name=="_transition")
function=Instrument().visit(function)
module=ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[]))
g.__dict__.update(movement=movement,fallback=fallback)
exec(compile(module,"<instrumented-no-restart>","exec"), g.__dict__)
word=[int(i%6==1) for i in range(90)]
word[9]=1
machine=g.OnlineGalil()
try:
    for symbol in word:
        while not machine.input_ready: machine.work()
        raw.append(symbol)
        machine.read("ab"[symbol])
    while not machine.input_ready: machine.work()
    print({"scope":"Python no-restart source execution", "checked_fallbacks":len(seen), "largest_radius":max((r for _,r,_,_ in seen),default=0), "violation":False}, flush=True)
except Violation:
    pass
