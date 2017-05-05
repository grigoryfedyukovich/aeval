#!/usr/bin/env python
from __future__ import print_function
import sys
import json
import argparse
from collections import defaultdict


def merge_dicts_of_lists(*args):
    m = {}
    for a in args:
        for k, v in a.iteritems():
            assert isinstance(v, list)
            m.setdefault(k, []).extend(v)
    return m


def sum_dicts_of_ints(*args):
    m = {}
    for a in args:
        for k, v in a.iteritems():
            assert isinstance(v, int)
            m[k] = m.get(k, 0) + v
    return m


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("PATHS", nargs='+')
    args = parser.parse_args()

    merged = {'times': defaultdict(lambda: defaultdict(list)),
              'iterCnts': defaultdict(lambda: defaultdict(list)),
              'unsuccessCnts': defaultdict(lambda: defaultdict(lambda: 0))}
    for path in args.PATHS:
        with open(path, 'r') as f:
            obj = json.load(f)
        for category in ['iterCnts', 'times']:
            for smttask in obj[category]:
                for hyperstr, contents in obj[category][smttask].iteritems():
                    merged[category][smttask][hyperstr].extend(contents)
        for smttask in obj['unsuccessCnts']:
            if isinstance(obj['unsuccessCnts'][smttask], int):
                print("old-style unsuccessCnts; skipping", file=sys.stderr)
                break
            for hyperstr in obj['unsuccessCnts'][smttask]:
                val = obj['unsuccessCnts'][smttask][hyperstr]
                merged['unsuccessCnts'][smttask][hyperstr] += val
    if len(merged['unsuccessCnts']) == 0:
        del merged['unsuccessCnts']
    json.dump(merged, sys.stdout)


if __name__ == '__main__':
    ret = main()
    if ret:
        sys.exit(ret)
