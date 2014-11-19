import sys, re
import pdelp_mo,RP_DeLPsolver_mo,pdelp,RP_DeLPsolver
from optparse import OptionParser
import socket
import sys
import json
import rpdelp_web
from xml.etree.ElementTree import Element, SubElement, Comment, tostring


def get_header_info(line):
#          t=re.match("^\#\sRP\-DeLP\sprogram\s\svars\:.*(\d+).*",line)
          #pattern="^#\sRP\-DeLP\sprogram\s\svars\:.*(\d+).*"
     pattern="^#\sRP-DeLP\sprogram,\svars\:\s+(\d+)\s+totalclauses\:\s+(\d+)\s+strict\spart\:\s+(\d+.\d+)\s+1st\slvl\:\s+(\d+.\d+)\s+maxclauselength\:\s+(\d+)\s*$"
     t=re.match(pattern,line)
     if t:
          n_vars,totalclauses,strict_part,fst_lvl,maxclaulen=t.groups()
          return {"number_vars":n_vars,"totalclauses":totalclauses,"strict_part":strict_part,"first_level":fst_lvl,"maxclaulen":maxclaulen}
     else:
          return {"number_vars":0,"totalclauses":0,"strict_part":0,"first_level":0,"maxclaulen":0}

def parse_input(list_in):
     #check for header
     header_info={}
     #inputs a file in a list
     program_levels=[]
     for line in list_in:
          if re.match(":strict",line):
               level=0
               program_levels.append([])
          elif re.match(":defeasible",line):
               level+=1
               program_levels.append([])
          elif re.match("\s",line):
               pass
          elif re.match("^#.*",line):
               header_info=get_header_info(line)
               print header_info
          elif re.match(":end",line):
               break
          else:
               for clause in line.split("."):
                    try: 
                         pdelp_mo.Clause(clause)
                    except Exception:
                         pass
                    else:
                         program_levels[level].append(clause+".")

     
     return header_info,program_levels

#capturar opcions
parser = OptionParser()
parser.add_option("-f", "--file", dest="infile",
                      help="reads FILE as input", metavar="FILE", default=None)
parser.add_option("-x", "--xml", dest="xmlfile",
                      help="reads XML FILE as input", metavar="FILE", default=None)
parser.add_option("-o", "--output", dest="output",
                      help="output computing options", metavar="", default=None)
parser.add_option("-s","--solver", dest="solver",
                      help="solver to use", default="")
parser.add_option("-d","--debug", 
                  action="store_true",dest="debug",
                  help="write debug to PATH", default=False)
(options, args) = parser.parse_args()

#evaluar opcions

if not options.solver:
    parser.error("one solving option is required")
else:
    if options.solver!="minisat" and options.solver!="clingo":
        parser.error("availabe solver options are minisat and clingo")

if not options.infile and not options.xmlfile:
        parser.error("an input file is required")

if not options.output:
     parser.error("one output option is required")
else:
    if options.output!="multiple" and options.output!="max-ideal":
        parser.error("availabe output options are multiple and max-ideal")

solver_options={
  "solver": options.solver,
  "output": options.output,
  "timeout":"8000",
  "file" : options.infile,
}

#escrivim a stderr per comprovar error
sys.stderr.write("in file: "+options.infile+"\n")
#fitxer a solucionar
program_levels=[]
level=0
if options.infile:
    f=open(options.infile,"r")
    header_info,program_levels=parse_input(f.readlines())

    xml_instance=rpdelp_web.generate_xml(program_levels[0],program_levels[1:])
    xml_file=rpdelp_web.save_xml(xml_instance)
    #escrivim a stderr per comprovar error                                                                                         
    sys.stderr.write("xml: "+xml_file+"\n")
#fname=rpdelp_web.save_xml(xml_file)



#llensar la query
if solver_options["output"]=="multiple":
    p=pdelp_mo.Program(xml_file)
    solution=RP_DeLPsolver_mo.solve(p,solver_options)
if solver_options["output"]=="max-ideal":
    p=pdelp.Program(xml_file)
    solution=RP_DeLPsolver.solve(p,solver_options)

rpdelp_web.delete_xml(xml_file)
#tractar output
if solution:
     
     xml_output=rpdelp_web.output_xml(p.stats,solution)
     #html_output=rpdelp_web.output_html(solution)
     stats={}
   
     stats.update(solver_options)
     #print solver_options  
     stats.update(header_info)
     #print header_info
     stats.update(solution)
     #print solution


     print stats

     j = json.dumps(stats, indent=4)
     res_namef=re.sub(".pdlp","-"+options.output+"-"+options.solver+".json",options.infile)
     f = open(res_namef, 'w')
     print >> f, j
     f.close()

     #f=open(res_namef+"-%s" % solver_options["solver"],"w")
     #f.write(tostring(xml_output))
     #f.close()
     

