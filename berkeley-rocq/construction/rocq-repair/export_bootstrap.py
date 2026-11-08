#!/usr/bin/env python3
"""Replay the literal bootstrap with a two-cell run-length accelerator.

This is an untrusted candidate generator: all resulting claims must be
checked against the literal table by the Rocq checker in Bootstrap.v.
"""
import argparse
import json
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TABLE = json.loads((HERE.parent / 'repairs/guarded-distinction/machine.json').read_text())['table']

# Pair bits (left, right), encoded as 0..3. Each stack is reversed, with top
# at the right. An absent suffix means an infinite tail of zero pairs.
def push(stack, pair, count=1):
    if not count or (pair == 0 and not stack):
        return
    if stack and stack[-1][0] == pair:
        stack[-1][1] += count
    else:
        stack.append([pair, count])

def pop(stack):
    if not stack:
        return 0
    pair, count = stack[-1]
    if count == 1:
        stack.pop()
    else:
        stack[-1][1] -= 1
    return pair

def top_run(stack, pair):
    if stack and stack[-1][0] == pair:
        return stack[-1][1]
    return 0

def drop(stack, n):
    if not n:
        return
    assert stack and n <= stack[-1][1]
    stack[-1][1] -= n
    if stack[-1][1] == 0:
        stack.pop()

def trans(q, b):
    w, d, r = TABLE[q][b]
    return w, d, r

def replay(limit, checkpoints):
    q, pair, half = 0, 0, 0
    left, right = [], []
    macro = steps = 0
    started = time.monotonic()
    while q != 73:
        if macro >= limit:
            raise RuntimeError(f'macro limit exceeded at {macro}')
        a, b = pair >> 1, pair & 1
        v = a if half == 0 else b
        w, d, q1 = trans(q, v)
        accelerated = False
        if half == 0 and d == 'R':
            w2, d2, q2 = trans(q1, b)
            if d2 == 'R' and q2 == q:
                n = 1 + top_run(right, pair)
                if n > 1:
                    drop(right, n - 1)
                    push(left, 2 * w + w2, n)
                    pair = pop(right)
                    steps += 2 * n
                    accelerated = True
        elif half == 1 and d == 'L':
            w2, d2, q2 = trans(q1, a)
            if d2 == 'L' and q2 == q:
                n = 1 + top_run(left, pair)
                if n > 1:
                    drop(left, n - 1)
                    push(right, 2 * w2 + w, n)
                    pair = pop(left)
                    steps += 2 * n
                    accelerated = True
        if not accelerated:
            pair = (2 * w + b) if half == 0 else (2 * a + w)
            q = q1
            if d == 'R':
                if half == 0:
                    half = 1
                else:
                    push(left, pair)
                    pair, half = pop(right), 0
            else:
                if half == 1:
                    half = 0
                else:
                    push(right, pair)
                    pair, half = pop(left), 1
            steps += 1
        macro += 1
        if checkpoints and macro % checkpoints == 0:
            print(f'{macro=}, {steps=}, {q=}, {half=}, {pair=}, left={len(left)}, right={len(right)}, elapsed={time.monotonic()-started:.1f}s', flush=True)
    print(f'end: {macro=}, {steps=}, {q=}, {half=}, {pair=}, left={left}, right={right}, elapsed={time.monotonic()-started:.1f}s', flush=True)
    return q, half, pair, left, right

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--limit', type=int, default=10000000)
    p.add_argument('--checkpoints', type=int, default=1000000)
    args = p.parse_args()
    replay(args.limit, args.checkpoints)
