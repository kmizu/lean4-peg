#!/usr/bin/env python3
"""Finite marker-free full-result comparison; not an all-input compiler proof."""
import sys,itertools
sys.dont_write_bytecode = True
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import partial_codeword_capture as p
END=p.seq(p.lit('#'),p.neg(p.A),p.P)
CHECK=p.seq(p.star(p.seq(p.lit('#'),p.P,p.look(p.lit('#')))),END)
LONG=p.look(p.seq(p.A,p.A))
ROOT=p.seq(p.look(p.call(0,p.RUN)),p.alt(p.seq(LONG,p.call(1,p.RUN,p.REST)),p.seq(p.neg(LONG),p.call(2,p.RUN))))
continuations=[p.lit(''),p.seq(p.lit('!'),p.P,p.EOF),p.seq(p.lit('a'),p.P),p.neg(p.P),p.star(p.lit(''))]
def whole(b):
    if b[0]=='param':return p.seq(p.P,p.Q) if b[1]==0 else ('param',b[1]+1)
    if b[0] in ('seq','alt'):return (b[0],tuple(map(whole,b[1])))
    if b[0] in ('not','star'):return (b[0],whole(b[1]))
    return b
count=0
for size in range(9):
 for chars in itertools.product('a#!',repeat=size):
  x=''.join(chars)
  for b in continuations:
   source=((1,p.seq(p.A,p.P,b)),)
   target=((1,CHECK),(2,p.seq(p.lit('#'),p.P,whole(b))),(1,p.seq(p.lit('#'),p.P,b)))
   a=p.evaluate(source,p.SOURCE_ROOT,x,True)
   c=p.evaluate(target,ROOT,x,False)
   if a!=c:raise AssertionError((x,b,a,c))
   count+=1
print('marker-free complete-result checks:',count)
