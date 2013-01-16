#! /usr/bin/python
from os import listdir
from subprocess import Popen, PIPE, STDOUT
import re
path = "./smlnj-lib"
dirList=listdir(path)
pat=re.compile('.*-sig\.sml')
for fname in dirList:
  if pat.match(fname):
    p = Popen("sml",stdin=PIPE,stdout=PIPE)
    p.communicate(input=('use "'+path+'/'+fname+'";'))
    p.stdin.close()

print "done\n"
