#!/usr/bin/env python
from __future__ import print_function
import os
import re
import sys
import math
import time
import json
import argparse
import tempfile
import subprocess


SUCCESS_ITERS_RE = re.compile(r'\s*\-+>\s+Success after (.*) iterations\s*')
ELAPSED_RE = re.compile(r'\s*elapsed: (.*)s\s*')
PROCS_TO_TRY = [1, 4]


class NoSuccessException(Exception):
    pass


def run_deephorn(example_path, proc_cnt, logs_dir_path):
    cmd = "/usr/bin/mpirun"
    retcode = subprocess.Popen(
        [cmd, "-mca", "btl", "^openib", "-n", str(proc_cnt),
            "-output-filename", os.path.join(logs_dir_path, "log"),
            "../../build/tools/deep/deephorn", example_path],
        env={"TMPDIR": "/tmp", "PATH": os.getenv("PATH")}).wait()
    if retcode != 0:
        raise subprocess.CalledProcessError(retcode, cmd)


def parse_log_dir_for_time(dirpath):
    """Returns seconds if any log in `path` is successful. Raises otherwise."""
    iter_cnt, elapsed_time = None, float('Inf')
    for filename in os.listdir(dirpath):
        with open(os.path.join(dirpath, filename), 'r') as f:
            for line in f.readlines()[-5:]:
                elapsed_match = ELAPSED_RE.match(line)
                iters_match = SUCCESS_ITERS_RE.match(line)
                if elapsed_match:
                    elapsed_fnd = float(elapsed_match.group(1))
                    elapsed_time = min(elapsed_time, elapsed_fnd)
                if iters_match:
                    iters_fnd = int(iters_match.group(1))
                    if iter_cnt is None or iters_fnd < iter_cnt:
                        iter_cnt = iters_fnd
    if iter_cnt is not None and not math.isinf(elapsed_time):
        return iter_cnt, elapsed_time
    raise NoSuccessException("no success in " + dirpath)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("SMTPATHS", nargs='+')
    parser.add_argument('--hist', action='store_true',
                        help="show histogram of times (only one smt)")
    parser.add_argument("-i", "--iters", default=100, type=int,
                        help="the number of times to run deephorn per pcnt")
    parser.add_argument("-o", "--outdir", type=str,
                        help="path to directory to save times and/or histograms")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    if args.hist and len(args.SMTPATHS) > 1:
        print("--hist only compatible with a single path", file=sys.stderr)
        return 1

    if args.outdir and not os.path.exists(args.outdir):
        os.makedirs(args.outdir)

    times = {s: {num: [] for num in PROCS_TO_TRY} for s in args.SMTPATHS}
    iter_cnts = {s: {num: [] for num in PROCS_TO_TRY} for s in args.SMTPATHS}
    unsuccess_cnts = {s: 0 for s in args.SMTPATHS}
    try:
        for i in range(args.iters):
            for spath in args.SMTPATHS:
                tmp_dir = tempfile.mkdtemp()
                if args.verbose:
                    print("tmpdir:", spath, "=", tmp_dir)
                for pcnt in PROCS_TO_TRY:
                    start = time.time()
                    run_deephorn(spath, pcnt, tmp_dir)
                    try:
                        i, t = parse_log_dir_for_time(tmp_dir)
                    except NoSuccessException:
                        t = time.time() - start
                        unsuccess_cnts[spath] += 1
                    times[spath][pcnt].append(t)
                    iter_cnts[spath][pcnt].append(i)
    except KeyboardInterrupt:
        pass

    # Save the times
    if args.outdir:
        with open(os.path.join(args.outdir, "times.json"), 'w') as f:
            json.dump({'times': times,
                       'iter_cnts': iter_cnts,
                       'unsuccess_cnts': unsuccess_cnts}, f)

    # Print the times
    for smtpath in times.iterkeys():
        subtime, subiters = times[smtpath], iter_cnts[smtpath]
        asterisk = ":"
        if unsuccess_cnts[smtpath]:
            asterisk = " [unsuccessful " + str(unsuccess_cnts[smtpath]) + "]:"
        print(smtpath + asterisk)
        for pcnt, t in subtime.iteritems():
            print("\t" + str(pcnt) + " process(es) took: " + str(sorted(t)))
        for pcnt, t in subiters.iteritems():
            print("\t" + str(pcnt) + " process(es) iterated: " + str(sorted(t)))

    # Draw histogram
    if args.hist:
        import matplotlib.pyplot as plt
        plt.hist(times.values()[0].values())
        plt.show()


if __name__ == '__main__':
    ret = main()
    if ret:
        sys.exit(ret)
