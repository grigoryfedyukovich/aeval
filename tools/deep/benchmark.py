#!/usr/bin/env python
import os
import re
import sys
import argparse
import tempfile
import subprocess


ELAPSED_RE = re.compile(r'\s*elapsed: (.*)s\s*')
PROC_NUMS_TO_TRY = [1, 4]


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
    """Returns seconds if any log in `path` is success. Raise otherwise."""
    for filename in os.listdir(dirpath):
        with open(os.path.join(dirpath, filename), 'r') as f:
            for line in f.readlines()[-5:]:
                m = ELAPSED_RE.match(line)
                if m:
                    return float(m.group(1))
    raise Exception("no success in " + dirpath)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("SMTPATHS", nargs='+')
    parser.add_argument("-i", "--iters", default=100, type=int,
                        help="the number of times to run deephorn per pcnt")
    args = parser.parse_args()

    times = {s: {num: [] for num in PROC_NUMS_TO_TRY} for s in args.SMTPATHS}
    try:
        for i in range(args.iters):
            for spath in args.SMTPATHS:
                tmp_dir = tempfile.mkdtemp()
                for pcnt in PROC_NUMS_TO_TRY:
                    run_deephorn(spath, pcnt, tmp_dir)
                    times[spath][pcnt].append(parse_log_dir_for_time(tmp_dir))
    except KeyboardInterrupt:
        pass

    # Print the times
    for smtpath, subtime in times.iteritems():
        print(smtpath + ":")
        for pcnt, t in subtime.iteritems():
            print("\twith " + str(pcnt) + " process(es), took: " + str(sorted(t)))

    # TODO: Draw histograms


if __name__ == '__main__':
    main()
