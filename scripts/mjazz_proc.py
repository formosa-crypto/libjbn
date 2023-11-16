import os
import sys
import ast
from string import Template

def bn_mjazz(argv0):
 script_directory = os.path.dirname(os.path.abspath(argv0))
 return (script_directory+"/../src/amd64/ref/mjazz_templates/")

def proc_entry(e, srcdir, dstdir):
 tfile = e[0] + '.mjazz'
 with open(srcdir + tfile) as fr:
  print("...process entry:", tfile)
  t = Template(fr.read())
  m = e[1]
  m['mjazzdir'] = dstdir
  p = t.substitute(**m)
  qualpref = ""
  if 'qual' in m: qualpref = m['qual'] + '_'
  pfile = dstdir + '/' + qualpref + e[0] + '.jinc'
  with open(pfile, 'w') as fw:
   fw.write(p)
 


def proc_file(mod):
 kfile = mod + ".keys"
 mjazzsrc = bn_mjazz(sys.argv[0])
 mjazzdst = mod #was: "mjazz_"+mod
 with open(kfile) as f: 
  kdata = ast.literal_eval(f.read())
  if not os.path.exists(mjazzdst): 
   print("...create directory '%s'" % (mjazzdst))
   os.makedirs(mjazzdst)
  else:
   print("...using existing directory: %s" % (mjazzdst))
  for e in kdata:
   proc_entry(e,mjazzsrc,mjazzdst)
 
def main():
 if len(sys.argv[1:])==1:
  mod = sys.argv[1]
  kfile = mod + ".keys"
  if os.path.isfile(kfile):
   print("Processing tags in %s" % (kfile))
   proc_file(mod)
  else:
   print("Cannot find tags file '%s'" % (kfile))
 else:
  print("usage: 'python3 mjazz_proc.py <module>'")
 
if __name__ == "__main__":
    main()


