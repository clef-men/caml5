import sys
import re
import glob

def print_usage() :
    print('usage: python3 setup.py [coq_pre_project_file]')
def error(msg) :
    print(f'error: {msg}')
    print_usage()
    exit(1)

def parse(line):
    if not line :
        return
    match = re.match(r'(?P<src>\S+)\s+->\s+(?P<dst>\S+)', line)
    if match :
        print('-Q {} {}'.format(match['src'], match['dst']))
        return
    match = re.match(r'-(?P<opt>\S+)', line)
    if match :
        print('-arg {}'.format(match['opt']))
        return
    match = re.match(r'(?P<filename>\S+.v)', line)
    if match :
        filename = match['filename']
        files = glob.glob(filename)
        if len(files) == 0 :
            error(f'no file matching: {filename}')
        for file in files :
            print(file)
        return
    error(f'cannot parse line: "{line}"')

if len(sys.argv) < 2 :
    error('missing arguments')
filename = sys.argv[1]

try :
    with open(filename) as file :
        for line in file.readlines() :
            parse(line.strip())
except OSError :
    error(f'cannot open file: {filename}')
