#!/usr/bin/env python
from __future__ import print_function
import os
import re
import sys
import time
import argparse
import tempfile
import subprocess


ELAPSED_RE = re.compile(r'\s*elapsed: (.*)s\s*')
PROC_NUMS_TO_TRY = [1, 4]


class NoSuccessException(Exception):
    pass


def run_deephorn(example_path, proc_cnt, logs_dir_path):
    cmd = "/usr/local/bin/mpirun"
    retcode = subprocess.Popen(
        [cmd, "-n", str(proc_cnt),
            "-output-filename", os.path.join(logs_dir_path, "log"),
            "../../build/tools/deep/deephorn", example_path],
        env={"TMPDIR": "/tmp", "PATH": os.getenv("PATH")}).wait()
    if retcode != 0:
        raise subprocess.CalledProcessError(retcode, cmd)


def parse_log_dir_for_time(dirpath):
    """Returns seconds if any log in `path` is successful. Raises otherwise."""
    for filename in os.listdir(dirpath):
        with open(os.path.join(dirpath, filename), 'r') as f:
            for line in f.readlines()[-5:]:
                m = ELAPSED_RE.match(line)
                if m:
                    return float(m.group(1))
    raise NoSuccessException("no success in " + dirpath)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("SMTPATHS", nargs='+')
    parser.add_argument('--hist', action='store_true',
                        help="show histogram of times (only one smt)")
    parser.add_argument("-i", "--iters", default=100, type=int,
                        help="the number of times to run deephorn per pcnt")
    args = parser.parse_args()

    if args.hist and len(args.SMTPATHS) > 1:
        print("--hist only compatible with a single path", file=sys.stderr)
        return 1

    times = {s: {num: [] for num in PROC_NUMS_TO_TRY} for s in args.SMTPATHS}
    unsuccess_cnts = {s: 0 for s in args.SMTPATHS}
    try:
        for i in range(args.iters):
            for spath in args.SMTPATHS:
                tmp_dir = tempfile.mkdtemp()
                for pcnt in PROC_NUMS_TO_TRY:
                    start = time.time()
                    run_deephorn(spath, pcnt, tmp_dir)
                    try:
                        t = parse_log_dir_for_time(tmp_dir)
                    except NoSuccessException:
                        t = time.time() - start
                        unsuccess_cnts[spath] += 1
                    times[spath][pcnt].append(t)
    except KeyboardInterrupt:
        pass

    # Print the times
    for smtpath, subtime in times.iteritems():
        asterisk = ":"
        if unsuccess_cnts[smtpath]:
            asterisk = " [unsuccessful " + str(unsuccess_cnts[smtpath]) + "]:"
        print(smtpath + asterisk)
        for pcnt, t in subtime.iteritems():
            print("\t" + str(pcnt) + " process(es) took: " + str(sorted(t)))

    # Draw histogram
    if args.hist:
        import matplotlib.pyplot as plt
        plt.hist(times.values()[0].values())
        plt.show()


if __name__ == '__main__':
    ret = main()
    if ret:
        sys.exit(ret)
