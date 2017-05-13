#!/usr/bin/env python
from __future__ import print_function
import os
import re
import sys
import math
import json
import argparse
import tempfile
import subprocess32
import traceback
from itertools import product, izip


SUCCESS_ITERS_RE = re.compile(r'\s*\-+>\s+Success after (.*) iterations\s*')
ELAPSED_RE = re.compile(r'\s*elapsed: (.*)s\s*')
PROCS_TO_TRY = [1, 4]


class NoSuccessException(Exception):
    pass


def name_only(path):
    return os.path.splitext(os.path.split(path)[1])[0].lower()


def run_deephorn(example_path, proc_cnt, aggprune, logs_dir_path):
    aggprune_arg = "0"
    if aggprune:
        aggprune_arg = "1"
    cmd = "/usr/bin/mpirun"
    proc = subprocess32.Popen(
        [cmd, "-mca", "btl", "^openib", "-n", str(proc_cnt),
            "-output-filename", os.path.join(logs_dir_path, "log"),
            "../../build/tools/deep/deephorn", "2000000", "1", "1",
            aggprune_arg, example_path],
        env={"TMPDIR": "/tmp", "PATH": os.getenv("PATH")})
    try:
        retcode = proc.wait(timeout=60*10)
    except subprocess32.TimeoutExpired:
        proc.kill()
        raise
    else:
        if retcode != 0:
            raise subprocess32.CalledProcessError(retcode, cmd)


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


def hyperps():
    return product(PROCS_TO_TRY, [True, False])


def hyperp_names():
    for p, a in hyperps():
        aname = "agg_off"
        if a:
            aname = "agg_on"
        yield str(p) + "," + aname


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("SMTPATHS", nargs='+')
    parser.add_argument('--hist', action='store_true',
                        help="show histogram of times (only one smt)")
    parser.add_argument("-i", "--iters", default=100, type=int,
                        help="the number of times to run deephorn per pcnt")
    parser.add_argument("-o", "--outdir", type=str,
                        help="path to directory to save times and/or histograms")
    parser.add_argument("--logdir", type=str,
                        help="path to directory to save logs")
    parser.add_argument("--hyper", type=str)
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    if args.hist and len(args.SMTPATHS) > 1:
        print("--hist only compatible with a single path", file=sys.stderr)
        return 1

    if args.logdir and os.path.exists(args.logdir):
        print("logdir already exists", file=sys.stderr)
        return 2

    if args.outdir and not os.path.exists(args.outdir):
        os.makedirs(args.outdir)

    times = {s: {k: [] for k in hyperp_names()} for s in args.SMTPATHS}
    iter_cnts = {s: {k: [] for k in hyperp_names()} for s in args.SMTPATHS}
    unsuccess_cnts = {s: {k: 0 for k in hyperp_names()} for s in args.SMTPATHS}
    try:
        if args.logdir:
            tmp_dir = args.logdir
        else:
            tmp_dir = tempfile.mkdtemp()
        for iter_ in xrange(args.iters):
            for spath in args.SMTPATHS:
                for (pcnt, aggprune), hypername in izip(hyperps(), hyperp_names()):
                    if args.hyper and args.hyper != hypername:
                        continue
                    log_path = os.path.join(tmp_dir, name_only(spath), hypername, str(iter_))
                    if args.verbose:
                        print("logs:", spath, "=", log_path)
                    os.makedirs(log_path)
                    try:
                        run_deephorn(spath, pcnt, aggprune, log_path)
                    except subprocess32.TimeoutExpired:
                        print("Timeout expired; marking as fail", file=sys.stderr)
                        unsuccess_cnts[spath][hypername] += 1
                        continue
                    except subprocess32.CalledProcessError:
                        traceback.print_exc()
                        continue
                    try:
                        i, t = parse_log_dir_for_time(log_path)
                        times[spath][hypername].append(t)
                        iter_cnts[spath][hypername].append(i)
                    except NoSuccessException:
                        unsuccess_cnts[spath][hypername] += 1

                # Checkpoint the times after each benchmark
                if args.outdir:
                    with open(os.path.join(args.outdir, "times.json"), 'w') as f:
                        json.dump({'times': times,
                                   'iterCnts': iter_cnts,
                                   'unsuccessCnts': unsuccess_cnts}, f)
    except KeyboardInterrupt:
        pass

    # Print the times
    for smtpath in times.iterkeys():
        subtime, subiters = times[smtpath], iter_cnts[smtpath]
        asterisk = ":"
        total_unsuc = sum(unsuccess_cnts[smtpath].values())
        if total_unsuc:
            asterisk = " [unsuccessful " + str(total_unsuc) + "]:"
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
