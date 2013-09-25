"""Unit testing framework for the Logo interpreter.

Usage: python3 scheme_test.py FILE

Interprets FILE as interactive Scheme source code, and compares each line
of printed output from the read-eval-print loop and from any output functions
to an expected output described in a comment.  For example,

(display (+ 2 3))
; expect 5

Differences between printed and expected outputs are printed with line numbers.
"""

import io
import sys
from buffer import Buffer
from scheme import read_eval_print_loop, create_global_frame
from scheme_tokens import tokenize_lines
from ucb import main

def summarize(output, expected_output):
    """Summarize results of running tests."""
    num_failed, num_expected = 0, len(expected_output)
    for (actual, (expected, line_number)) in zip(output, expected_output):
        if expected.startswith("Error"):
            if not actual.startswith("Error"):
                num_failed += 1
                print('test failed at line {0}'.format(line_number))
                print('  expected an error indication')
                print('   printed: {0}'.format(actual))
        elif actual != expected:
            num_failed += 1
            print('test failed at line {0}'.format(line_number))
            print('  expected: {0}'.format(expected))
            print('   printed: {0}'.format(actual))
    print('{0} tested; {1} failed.'.format(num_expected, num_failed))

EXPECT_STRING = '; expect'

class TestReader(object):
    """A TestReader is an iterable that collects test case expected results."""
    def __init__(self, lines):
        self.lines = lines
        self.expected_output = []
        self.line_number = 0

    def __iter__(self):
        for line in self.lines:
            line = line.rstrip('\n')
            self.line_number += 1
            if line.lstrip().startswith(EXPECT_STRING):
                expected = line.split(EXPECT_STRING, 1)[1][1:]
                self.expected_output.append((expected, self.line_number))
            yield line
        raise EOFError

@main
def run_tests(src_file = 'tests.scm'):
    """Run a read-eval loop that reads from src_file and collects outputs."""
    sys.stderr = sys.stdout = io.StringIO() # Collect output to stdout and stderr
    try:
        reader = TestReader(open(src_file).readlines())
        src = Buffer(tokenize_lines(reader))
        def next_line():
            src.current()
            return src
        read_eval_print_loop(next_line, create_global_frame())
    except BaseException as exc:
        sys.stderr = sys.__stderr__
        print("Tests terminated due to unhandled exception "
              "after line {0}:\n>>>".format(reader.line_number),
              file=sys.stderr)
        raise
    output = sys.stdout.getvalue().split('\n')
    sys.stdout = sys.__stdout__  # Revert stdout
    summarize(output, reader.expected_output)
