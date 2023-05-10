import sys
import re
import glob
import io

out = io.StringIO()
def output(str) :
    print(str, file = out)

def print_usage() :
    print('usage: python3 setup.py [coq_pre_project_file]', file = sys.stderr)
def error(msg) :
    print(f'error: {msg}', file = sys.stderr)
    print_usage()
    exit(1)

def parse(line):
    if not line :
        return
    match = re.match(r'(?P<src>\S+)\s+->\s+(?P<dst>\S+)', line)
    if match :
        output('-Q {} {}'.format(match['src'], match['dst']))
        return
    match = re.match(r'-w\s+(?P<warning>\S+)', line)
    if match :
        output('-arg -w -arg {}'.format(match['warning']))
        return
    match = re.match(r'-(?P<opt>\S+)', line)
    if match :
        output('-arg {}'.format(match['opt']))
        return
    match = re.match(r'(?P<filename>\S+.v)', line)
    if match :
        filename = match['filename']
        files = glob.glob(filename)
        if len(files) == 0 :
            error(f'no file matching: {filename}')
        for file in files :
            output(file)
        return
    error(f'cannot parse line: "{line}"')

if len(sys.argv) < 2 :
    error('missing arguments')
filename = sys.argv[1]

try :
    with open(filename) as file :
        for line in file.readlines() :
            parse(line.strip())
        print(out.getvalue(), end = '')
except OSError :
    error(f'cannot open file: {filename}')
out.close()
