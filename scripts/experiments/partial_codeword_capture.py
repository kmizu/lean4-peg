#!/usr/bin/env python3
"""Finite differential experiment; not an all-input translation proof.

The source capture ends inside its last a*# block. The target uses one
origin preflight and two consecutive captures to retain the entire value.
Both grammars are fixed independently of block length and repetition count.
"""
from functools import lru_cache
from itertools import product


def seq(*xs):
    return ('seq', xs)


def alt(*xs):
    return ('alt', xs)


def lit(s):
    return ('lit', s)


def star(x):
    return ('star', x)


def neg(x):
    return ('not', x)


def look(x):
    return neg(neg(x))


def call(i, *args):
    return ('call', i, args)


P = ('param', 0)
Q = ('param', 1)
RUN = star(lit('a'))
A = seq(RUN, lit('#'))
B = seq(star(seq(A, look(A))), RUN)
EOF = neg(('any',))
SOURCE = ((1, seq(A, P, lit('!'), P, EOF)),)
SOURCE_ROOT = call(0, B)
# Check every complete block and the final partial block against the first
# a-run. The lookahead keeps the last shifted replay out of the loop.
CHECK = seq(star(seq(lit('#'), P, look(lit('#')))), lit('#'), P)
REST = seq(lit('#'), star(seq(A, look(A))), RUN)
TARGET = (
    (1, seq(CHECK, look(lit('!')))),
    (2, seq(lit('#'), P, lit('!'), P, Q, EOF)),
    (1, seq(lit('#'), P, lit('!'), P, EOF)),
)
LONG = look(seq(A, A))
TARGET_ROOT = seq(look(call(0, RUN)), alt(
    seq(LONG, call(1, RUN, REST)),
    seq(neg(LONG), call(2, RUN)),
))
FAIL = -1
UNDEFINED = -2


def evaluate(grammar, root, text, parallel):
    """Forward offsets; arguments all use the original caller environment.

    Parallel arguments start at the caller origin. Sequential arguments
    start at the previous endpoint. A successful call replaces the callee
    environment with the argument captures and restores the caller on return.
    """
    @lru_cache(None)
    def ev(expr, pos, env):
        op = expr[0]
        if op == 'lit':
            return pos + len(expr[1]) if text.startswith(expr[1], pos) else FAIL
        if op == 'param':
            return ev(lit(env[expr[1]]), pos, env) if expr[1] < len(env) else FAIL
        if op == 'any':
            return pos + 1 if pos < len(text) else FAIL
        if op == 'not':
            end = ev(expr[1], pos, env)
            return UNDEFINED if end == UNDEFINED else pos if end == FAIL else FAIL
        if op == 'seq':
            for child in expr[1]:
                pos = ev(child, pos, env)
                if pos < 0:
                    return pos
            return pos
        if op == 'alt':
            for child in expr[1]:
                end = ev(child, pos, env)
                if end != FAIL:
                    return end
            return FAIL
        if op == 'star':
            while True:
                end = ev(expr[1], pos, env)
                if end == FAIL:
                    return pos
                if end == UNDEFINED or end == pos:
                    return UNDEFINED
                pos = end
        if op == 'call':
            arity, body = grammar[expr[1]]
            assert arity == len(expr[2])
            vals, end = [], pos
            for arg in expr[2]:
                start = pos if parallel else end
                end = ev(arg, start, env)
                if end < 0:
                    return end
                vals.append(text[start:end])
            return ev(body, pos if parallel else end, tuple(vals))
        raise AssertionError(op)
    return ev(root, 0, ())


def expected(text):
    """Independent description u^(n+1) a^k ! u^n a^k, u=a^k#."""
    if text.count('!') != 1:
        return False
    left, right = text.split('!')
    k = len(left) - len(left.lstrip('a'))
    unit = 'a' * k + '#'
    count = left.count('#')
    return count > 0 and left == unit * count + 'a' * k and right == unit * (count - 1) + 'a' * k


def check(text):
    source = evaluate(SOURCE, SOURCE_ROOT, text, True)
    target = evaluate(TARGET, TARGET_ROOT, text, False)
    want = len(text) if expected(text) else FAIL
    assert source == target == want, (repr(text), source, target, want)


def main():
    count = 0
    for length in range(10):
        for word in product('a#!', repeat=length):
            check(''.join(word))
            count += 1
    # Longer generated positives and mutations cover unbounded-phase candidates
    # beyond the exhaustive length bound; this remains finite evidence.
    cases = set()
    for k in range(9):
        for n in range(9):
            unit = 'a' * k + '#'
            word = unit * (n + 1) + 'a' * k + '!' + unit * n + 'a' * k
            cases.add(word)
            for i in range(len(word)):
                cases.add(word[:i] + word[i + 1:])
                cases.add(word[:i] + ('#' if word[i] == 'a' else 'a') + word[i + 1:])
            cases.add(word + 'a')
            cases.add('b' + word)
    for word in cases:
        check(word)
    print(f'PASS: {count} exhaustive strings (length <= 9), {len(cases)} generated/mutated strings')
    print('Both fixed grammars agree with the independent language description on these cases.')
    print('All-input equivalence, partial observations, recursive integration remain unproved.')


if __name__ == '__main__':
    main()
