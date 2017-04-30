#!/usr/bin/env python
from __future__ import print_function
import os
import re
import sys
import json
import argparse
import subprocess
from collections import defaultdict


TOTAL_TIME_RE = re.compile(r'\s*[tT]otal [tT]ime:?\s+([\.0-9]*)\s*')


# TODO: Should actually check for explicit success, not just total time report
class NoSuccessException(Exception):
    pass


def getenv_or_raise(v):
    r = os.getenv(v)
    if r is None:
        raise Exception("environment variable %s not set" % v)
    return r

# TODO: Note that /printAssignment and /trace option is for interactive runs and might cause a significant slowdown.
def run_ice(example_path):
    """Returns ICE Boogie.exe on `example_path`. Returns runtime on success."""
    assert os.path.isfile(example_path)
    root = getenv_or_raise("ICE_ROOT")
    cmd = os.path.join(root, "Boogie", "Binaries-Full", "Boogie.exe")
    assert os.path.isfile(cmd)
    output = subprocess.check_output([cmd, "/nologo", "/noinfer",
                                      "/contractInfer", "/ice",
                                      "/printAssignment", example_path])
    for line in output.splitlines()[-10:]:
        m = TOTAL_TIME_RE.match(line)
        if m:
            return float(m.group(1))
    raise NoSuccessException("couldn't find 'Total time'")


def ice_benchmarks():
    root = getenv_or_raise("ICE_ROOT")
    bench_root = os.path.join(root, "benchmarks")
    assert os.path.isdir(bench_root)
    for root, dirs, files in os.walk(bench_root):
        for f in files:
            if os.path.splitext(f)[1].lower() == ".bpl":
                yield os.path.join(root, f)


def run_mcmc(example_dirpath):
    root = getenv_or_raise("MCMC_ROOT")
    cmd = os.path.join(root, "Release", "numerical.exe")
    assert os.path.isfile(cmd)
    output = subprocess.check_output([cmd], cwd=example_dirpath)
    for line in output.splitlines()[-10:]:
        m = TOTAL_TIME_RE.match(line)
        if m:
            return float(m.group(1))
    raise NoSuccessException("couldn't find 'Total time'")


def mcmc_benchmarks():
    # Gather all directories with .xml in 'em
    root = getenv_or_raise("MCMC_ROOT")
    bench_root = os.path.join(root, "benchmarks", "numerical")
    assert os.path.isdir(bench_root)
    for root, dirs, files in os.walk(bench_root):
        for f in files:
            if os.path.splitext(f)[1].lower() == ".xml":
                yield root
                break


def name_only(path):
    return os.path.splitext(os.path.split(path)[1])[0].lower()


def bench_intersection(a, b):
    a_set = set(name_only(path) for path in a)
    b_set = set(name_only(path) for path in b)
    i = a_set.intersection(b_set)
    return ([x for x in a if name_only(x) in i],
            [x for x in b if name_only(x) in i])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("BENCHNAMES", nargs='*')
    parser.add_argument('--mcmc', action='store', type=int, default=5,
                        help="run the MCMC solver N iterations")
    parser.add_argument('--ice', action='store', type=int, default=5,
                        help="run the ICE (Boogie.exe) solver N iterations")
    parser.add_argument("-o", "--outfile", type=str,
                        help="path to file to save times")
    parser.add_argument('-r', "--resume", action='store_true',
                        help="merge results with outfile if it exists")
    parser.add_argument('-v', "--verbose", action='store_true',
                        help="be noisier about what's going on")
    args = parser.parse_args()

    if not args.resume and args.outfile and os.path.exists(args.outfile):
        print("'%s' already exists" % args.outfile, file=sys.stderr)
        return 1

    times, others = {}, []
    if args.resume and os.path.exists(args.outfile):
        with open(args.outfile, 'r') as f:
            times = json.load(f)['times']
    times = defaultdict(lambda: defaultdict(list), {k: defaultdict(list, {a: b for a, b in v.iteritems()})
                                                    for k, v in times.iteritems()})

    try:
        # Construct name-only set of benchmarks to run
        if args.BENCHNAMES:
            lc_benchnames = set(l.lower() for l in args.BENCHNAMES)
        else:
            orig_sets = []
            if args.mcmc:
                orig_sets.append(set(name_only(b) for b in mcmc_benchmarks()))
            if args.ice:
                orig_sets.append(set(name_only(b) for b in ice_benchmarks()))
            lc_benchnames = orig_sets[0]
            for s in orig_sets[1:]:
                lc_benchnames.intersection_update(s)
            if args.verbose:
                print("Running benchmarks:", ', '.join(lc_benchnames))

        if args.mcmc:
            b = list(mcmc_benchmarks())
            if len(b) == 0:
                raise Exception("No benchmarks for MCMC found")
            b = [x for x in b if name_only(x) in lc_benchnames]
            others.append(("MCMC", run_mcmc, args.mcmc, b))
        if args.ice:
            b = list(ice_benchmarks())
            if len(b) == 0:
                raise Exception("No benchmarks for ICE found")
            b = [x for x in b if name_only(x) in lc_benchnames]
            others.append(("ICE", run_ice, args.ice, b))
        for n, fn, cnt, benches in others:
            for b in benches:
                t_list = times[n][name_only(b)]
                while len(t_list) < cnt:
                    if args.verbose:
                        print("Running %s on %s" % (n, name_only(b)))
                    t_list.append(fn(b))
    except KeyboardInterrupt:
        pass

    # Save the times
    if args.outfile:
        with open(args.outfile, 'w') as f:
            json.dump({'times': times}, f)

    # Print the times
    for k, v in times.iteritems():
        print(k, ":")
        for benchpath, t in v.iteritems():
            t = list(t)
            if len(t):
                print("  ", name_only(benchpath), ": ", t)


if __name__ == '__main__':
    ret = main()
    if ret:
        sys.exit(ret)
