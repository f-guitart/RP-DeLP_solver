import sys, re, os, copy
from optparse import OptionParser
import __builtin__

from pdelp_mo import Literal, Clause, Program, not_depend, conflict, rulesCache, almostValidCache, stack, inverseRulesList, is_prevalid, generates_conflict, almostValidList, inverseList, reasonList
from PySAT import ConjunctiveNormalFormula
import time
from xml.etree.ElementTree import Element, SubElement, Comment, tostring, parse

SATSOLVERS=["minisat","glucose","clingo"]
HOMEPATH="/home/francesc/doctorat/solver-RPDeLP/"
__builtin__.CLINGOPATH="/usr/bin/"
__builtin__.MINISATPATH="/usr/bin/"
__builtin__.GLUCOSEPATH="/usr/local/bin/"
__builtin__.CONFLENCTIME=0
__builtin__.ALMVALENCTIME=0
__builtin__.DEBUG=False
class validLiteralsList(object):

    def __init__(self,vc):
        self.list={}
        self.length=0
        self.visited=0
        self.valid=self.length
        self.insert(vc)
        self.current_item=0
        self.val_cyc_con=self.length
        
    def insert(self,lit):
        if type(lit) is list:
            for l in lit:
                self.insert(l)
        else:
            if not self.exists(lit):
                #              Valid, Visited,Cycle,Conflict
                self.list[lit]=[True,False,None,None]
                self.valid+=1
                self.length+=1
            else:
                #prova
                if self.is_valid(lit):
                    pass
                else:
                    self.set_valid(lit)
                #raise Exception("This literal already exists in ValidLiterals list!")

    def update(self,new_vc):
        '''updates vL and returns new valid literals'''
        vc=[]
        for lit in new_vc:
            if not self.exists(lit):
                self.insert(lit)
                vc.append(lit)
                self.val_cyc_con+=1
        return vc

    def delete(self,lit):
        if self.is_visited(lit):
            self.visited-=1
        if self.is_valid(lit):
            self.valid-=1
        self.length-=1
        self.list.pop(lit)

    def set_visited(self,lit):
        if not self.is_visited(lit):
            self.list[lit][1]=True
            self.visited+=1

    def unset_visited(self,lit):
        if self.is_visited(lit):
            self.list[lit][1]=False
            self.visited-=1

    def set_valid(self,lit):
        if not self.is_valid(lit):
            self.list[lit][0]=True
            self.valid+=1

    def unset_valid(self,lit):
        if self.is_valid(lit):
            self.list[lit][0]=False
            self.valid-=1
        if self.list[lit][2]==None and self.list[lit][3]==None:
            self.val_cyc_con-=1

    def exists(self,lit):
        if lit in self.list.keys():
            return True
        else:
            return False

    def all_visited(self):
        return self.visited==self.length

    def none_valid(self):
        return self.valid==0

    def empty(self):
        return self.length==0

    def is_valid(self,lit):
        return self.exists(lit) and self.list[lit][0]==True

    def is_visited(self,lit):
        return self.exists(lit) and self.list[lit][1]==True

    def is_cycle(self,lit):
        if self.exists(lit):
            return self.list[lit][2] is True

    def is_conflict(self,lit):
        if self.exists(lit):
            return self.list[lit][3] is True

    def set_cycle(self,lit):
        if self.exists(lit):
            self.list[lit][2]=True
        if self.list[lit][0]==True and self.list[lit][3]==None:
            self.val_cyc_con+=-1

    def set_conflict(self,lit):
        if self.exists(lit):
            self.list[lit][3]=True

        if self.list[lit][0]==True and self.list[lit][2]==None:
            self.val_cyc_con+=-1

    def set_no_cycle(self,lit):
        if self.exists(lit):
            self.list[lit][2]=False

    def set_no_conflict(self,lit):
        if self.exists(lit):
            self.list[lit][3]=False

    def update_to_no_conflict(self):
        for key,value in self.list.items():
            if self.list[key][3]!=None and self.list[key][2]==None and self.list[key][0]==True:
                #c=raw_input("*****        updt no cnflct")
                self.val_cyc_con+=1
            self.list[key][3]=None

    def update_to_no_cycle(self):
        for key,value in self.list.items():
            if self.list[key][2]!=None and self.list[key][3]==None and self.list[key][0]==True:
                #c=raw_input("*****        updt no cycle")
                self.val_cyc_con+=1
            self.list[key][2]=None

    def __iter__(self):
        return self

    def next(self):
        if self.val_cyc_con==0:
            raise StopIteration
        else:
            if self.current_item<len(self.list)-1:
                self.current_item+=1
            else:
                self.current_item=0
            if self.is_valid(self.list.items()[self.current_item][0]) and\
                    not self.is_cycle(self.list.items()[self.current_item][0]) and\
                    not self.is_conflict(self.list.items()[self.current_item][0]):
                return self.list.items()[self.current_item]
            else:
                return self.next()
            

def cycle(cycle_iter):
    '''We define a cycle when after an iteration
    the valid literals list does not change'''

    return cycle_iter[0]-cycle_iter[1]>=2


def update_valid_literals(program, W,B, literal, level):
    #tenir una llista inversa de les regles que continguin literal al cos
    #per totes aquestes regles, coprovar que ttots els literals estiguin en W
    new_vc=[]
    a=inverseList()
    #dict que conte el body dels literals
    subarg_dict={}

    for rules in program.inverseList:   
        if literal in rules.keys():
            for rule,lvl in rules[literal]:
                print rule
                if is_prevalid(rule,W,B) and not generates_conflict(program,rule.head,W) and int(lvl)<=int(level):
                    print "is prevalid"
                    new_vc.append(rule.head)
                    subarg_dict[rule.head]=rule.body
                print "is not prevalid"
    return new_vc,subarg_dict

def level_computing(program,ext,O,S,W,W_r,B,B_r,level,solver):
    vc=program.get_valid_literals(W,B,level)
    print "--->Valid literals:",vc
    #W=program.get_warranted(0,level)
    #B=program.get_blocked(0,level)
    recursive_extension(program,ext,O,S,W,W_r,B,B_r,level,vc,solver)
    va=S.pop()
    return va

def output_exists(O,W,B,level):
    
    for output in O:
        if set(W) == set(output[0]) and  set(B) == set(output[1]):
            return True
    return False

def recursive_extension(program, ext, O, S, W, W_r, B, B_r, level, vc, solver):
    
    #TODO: veure com ho fem lo de la almost valid cache
    #program.almostValidCache=almostValidCache()
    #Dict where literals are set as visited and valid
    vL=validLiteralsList(vc)
    #almost valid list in order to mantain some queries in a list
    #and avoid launching the sat query
    av_list=almostValidList()
    #Literals that for sure will generate a conflict
    conflictiveLiterals=[]
    #Cycle iterator
    cycle_iter=[0,0]
    #check if it is in the max level of recursion
    is_leaf=True
    #subarguments dict:
    subarg_dict={}


    print "[ Enter recursive extension ]: ",W,B,vc
    while vL.none_valid() is False and is_leaf:
        cycle_iter[0]+=1
        #while i<len(vc) and vL.all_visited() is False:
        for valid_literal in vL:
            literal=valid_literal[0]
            notDepend=not_depend(program, W, B, literal, vc, av_list, level, solver)
            conf,c_lit=conflict(program,level,literal,vc,W,notDepend,1,solver)
            cycl= cycle(cycle_iter)
            if not cycl and not conf:
                W.append(literal)
                print "Literal ",literal," added in warrant"
                if literal in subarg_dict.keys():
                    prod_rule=subarg_dict[literal]
                else:
                    prod_rule=literal
                print "aloha!"
                W_r.add(literal,program.rulesList.get_producing_rule2(program,literal,W),level)
                print W_r

                vL.unset_valid(literal)
                vc.remove(literal)
                #returns new activated literals
                new_vc,subarg_dict=update_valid_literals(program,W,B,literal,level)
                print "--->New valid literals",new_vc
                #returns valid literals not in vL (removes already existent in vL)
                new_vc2=vL.update(new_vc)

                vc=vc+new_vc2
                cycle_iter[1]=cycle_iter[0]
                vL.update_to_no_cycle()  
                
            else:
                if cycl:
                    vL.set_cycle(literal)
                if conf:
                    vL.set_conflict(literal)
        I=[]

        for literal in vc:
            if vL.is_valid(literal):
                confl,c_lit=conflict(program,level,literal,vc,W,None,2,solver)
                if confl:
                    I.append(literal)
                    cycle_iter[1]=cycle_iter[0]
                    for lit in c_lit:
                        if lit in W:
                            c_lit.remove(lit)
		    #p.get_producing_rule2(p,literal)--->es una xapusa	
                    B_r.add(literal,(c_lit,program.rulesList.get_producing_rule2(program,literal,W)),level)
                else:
                    pass
        B=B+I
        for literal in I:
            vL.unset_valid(literal)
            vc.remove(literal)
            #program.almostValidCache.update(literal)
            vL.update_to_no_cycle()
            vL.update_to_no_conflict()

        J=[]
        if cycle(cycle_iter):
            J=copy.copy(vc)
        for literal in J:
            W_ext=copy.copy(W)
            W_ext.append(literal)
            W_r_ext=copy.copy(W_r)
            print "Literal ",literal," added in warrant"
            vc_ext=copy.copy(vc)
            vc_ext.remove(literal)
            new_vc,subarg_dict=update_valid_literals(program,W_ext,B,literal,level)

            if literal in subarg_dict.keys():
                    prod_rule=subarg_dict[literal]
            else:
                prod_rule=literal
            W_r_ext.add(literal,program.rulesList.get_producing_rule2(program,literal,W_ext),level)
            print W_r


            for l in new_vc:
                if l not in vc_ext:
                    vc_ext.append(l)
            recursive_extension(program,ext,O,S,W_ext,W_r_ext,B,B_r,level,vc_ext,solver)

        if len(J) > 0:
            is_leaf=False
            

    if S.is_not_in(W,B,level) and is_leaf:
        print S
        print "-----------------------"
        print W,B,level
#        c=raw_input("------------------------")
        S.push(W,W_r,B,B_r,level)
        if level == program.get_max_level()-1:
            O.append([W,W_r,B,B_r,level,time.time()])
            program.stats.add_time(time.time()-program.stats.t1)


def solve(p,options):
    __builtin__.DEBUG=True
        
    if options["solver"]=="clingo":
        __builtin__.ASP=True
        __builtin__.SAT=False
        solver_method="asp" 
        solver=options["solver"]
    elif options["solver"]=="glucose" or options["solver"]=="minisat":
        __builtin__.ASP=False
        __builtin__.SAT=True
        solver_method="sat" 
        solver=options["solver"]

    if os.uname()[1]=="am.udl.cat":
         __builtin__.ENCODINGPATH="/home/fguitart/solver-RPDeLP/debug/"
         __builtin__.MINISATPATH="/home/fguitart/soft/minisat/core/"
         __builtin__.CLINGOPATH="/home/fguitart/soft/clingo/"
         __builtin__.GLUCOSEPATH="/home/fguitart/soft/glucose_2.0/"
         
    elif re.match("compute-\d+-\d+\.local", os.uname()[1]): 
        __builtin__.ENCODINGPATH="/state/partition1/"
        __builtin__.MINISATPATH="/home/fguitart/soft/minisat/core/"
        __builtin__.CLINGOPATH="/home/fguitart/soft/clingo/"
        __builtin__.GLUCOSEPATH="/home/fguitart/soft/glucose_2.0/"

    elif re.match("arinf.udl.cat", os.uname()[1]): 
        __builtin__.CLINGOPATH="/home/francesc/bin/clingo/"
        __builtin__.MINISATPATH="/home/francesc/bin/minisat/"
        #al server ara no hi es, s'ha d'instalar
        __builtin__.GLUCOSEPATH="/home/francesc/bin/glucose/glucose"
        __builtin__.ENCODINGPATH="/home/francesc/argumentation/debug/"
    else:
        #__builtin__.CLINGOPATH="/usr/bin/"
        __builtin__.CLINGOPATH=""
        #__builtin__.MINISATPATH="/usr/bin/"
        __builtin__.MINISATPATH=""
        __builtin__.GLUCOSEPATH="/usr/local/bin/"
        #__builtin__.ENCODINGPATH="/home/francesc/doctorat/argumentation/solvers/debug/"
        SCRPATH=os.path.realpath(__file__)
        t=re.match('(.*)/RP_DeLPsolver_mo.py',SCRPATH)
        if t:
            ENCPATH=t.group(1)
        __builtin__.ENCODINGPATH=ENCPATH+"/debug/"
    
        if not os.path.exists(__builtin__.ENCODINGPATH):
            os.makedirs(__builtin__.ENCODINGPATH)


    #variable global per emmagatzemar el temps d'encoding
    __builtin__.CONFLENCTIME=0
    __builtin__.ALMVALENCTIME=0
    
    solver=options["solver"]

    t1=time.time()

    stats={}
    #stats['file']="0"
    #stats['solver']="0"
    #stats['variables']="0"
    #stats['clauses']="0"
    #stats['strict part']="0"
    #stats['defeasible part']="0"
    #stats['levels']="0"
    stats['consistent']=True

    sk=p.get_strict_knowledge()

    if sk==False:
        #print "Base de coneixement no consistent"
        p.stats.knowBase=False
        stats['consistent']=False
        stats['times']=str(time.time()-t1)
        
        return stats
    
    max_level= p.get_max_level()
    S=stack()
    ext=0
    O=[]
    alpha=0
    W_r=reasonList()
    B_r=reasonList()

    W=p.get_warranted()

    for wlit in W:
        W_r.add(wlit,p.rulesList.get_producing_rule2(p,wlit,W),0)

    S.push(W,W_r,[],B_r,0)

    while not S.is_empty():
        W,W_r,B,B_r,alpha=S.pop()
        while alpha <= max_level:
            alpha+=1
            W,W_r,B,B_r,alpha=level_computing(p,ext,O,S,W,W_r,B,B_r,alpha,solver)


    stats['warrant_list']=[]
    stats['blocked_list']=[]
    for o in O:
        stats['warrant_list'].append([])
        stats['blocked_list'].append([])
        for warr_lit in o[0]:
            #literal,reason,level
            print "****",warr_lit,o[1][warr_lit][0][0],o[1][warr_lit][0][1]
            stats['warrant_list'][-1].append((warr_lit,o[1][warr_lit][0][0],o[1][warr_lit][0][1]))
	for block_lit in o[2]:
	    print "@@@@ ",block_lit,"conflict",o[3][block_lit][0][0][0],block_lit,o[3][block_lit][0][0][1],block_lit,o[3][block_lit][0][1]
	    #print "****",block_lit,"conflict",[0],o[3][block_lit][0][1]
	    stats['blocked_list'][-1].append((block_lit,"conflict",o[3][block_lit][0][0][0],o[3][block_lit][0][0][1],o[3][block_lit][0][1]))
            #stats['blocked_list'][-1].append((block_lit,"conflict",o[3][block_lit][0][0],o[3][block_lit][0][1]))

    solving_time=time.time()-t1
    stats["time"]=solving_time
    stats['n_outputs']=len(O)
    stats['times']=p.stats.times
    return stats

    
if __name__ == '__main__':

    parser = OptionParser()
    parser.add_option("-f", "--file", dest="filename",
                      help="reads FILE as input", metavar="FILE", default=None)
    parser.add_option("-o", "--output", dest="output",
                      help="write report to FILE", metavar="FILE", default=None)
    parser.add_option("-s","--sat", dest="satsolv",
                      help="use SAT encoding", default="")
    parser.add_option("-a","--asp" ,dest="aspsolv",
                      help="use ASP encoding", default="")

    parser.add_option("-d","--debug", 
                      action="store_true",dest="debug",
                      help="write debug to PATH", default=False)

    (options, args) = parser.parse_args()

    if options.satsolv and options.aspsolv:
        parser.error("options -a and -s are mutually exclusive")
    elif options.satsolv and not options.aspsolv:
        if options.satsolv not in SATSOLVERS:
            parser.error("unknown sat solver. available sat solvers are %s" % SATSOLVERS)

    if not options.satsolv and not options.aspsolv:
        parser.error("one solving option is required")
    if not options.filename:
        parser.error("an input file is required")

    print options.filename
    print options.output
    print options.satsolv
    print options.aspsolv


    __builtin__.DEBUG=options.debug
 
        
    if options.aspsolv:
        __builtin__.ASP=True
        __builtin__.SAT=False
        solver_method="asp" 
        solver=options.aspsolv 
    elif options.satsolv:
        __builtin__.ASP=False
        __builtin__.SAT=True
        solver_method="sat" 
        solver=options.satsolv

    if os.uname()[1]=="am.udl.cat":
         __builtin__.ENCODINGPATH="/home/fguitart/solver-RPDeLP/debug/"
         __builtin__.MINISATPATH="/home/fguitart/soft/minisat/core/"
         __builtin__.CLINGOPATH="/home/fguitart/soft/clingo/"
         __builtin__.GLUCOSEPATH="/home/fguitart/soft/glucose_2.0/"
         
    elif re.match("compute-\d+-\d+\.local", os.uname()[1]): 
        __builtin__.ENCODINGPATH="/state/partition1/"
        __builtin__.MINISATPATH="/home/fguitart/soft/minisat/core/"
        __builtin__.CLINGOPATH="/home/fguitart/soft/clingo/"
        __builtin__.GLUCOSEPATH="/home/fguitart/soft/glucose_2.0/"
    else:
        __builtin__.CLINGOPATH="/usr/bin/"
        __builtin__.MINISATPATH="/usr/bin/"
        __builtin__.GLUCOSEPATH="/usr/local/bin/"
        __builtin__.ENCODINGPATH="/home/francesc/doctorat/solver-RPDeLP/debug/"
    

    #variable global per emmagatzemar el temps d'encoding
    __builtin__.CONFLENCTIME=0
    __builtin__.ALMVALENCTIME=0

    t1=time.time()
    p=Program(options.filename)

    if not options.output:
        res_namef=re.sub(".pdlp",".res",options.filename)
    else:
        res_namef=options.output


    f = open(options.filename,"r")
    filecomments=""
    for line in f.readlines():
        if(re.match("#.*",line)):
            filecomments=filecomments+line
    if(len(filecomments)==0): filecomments="# Pdlep program\n"
    f.close()



    f = open(res_namef+"-"+solver,"w")
    f.write(filecomments)
    f.writelines("File solved: %s\n" % options.filename)
    f.writelines("Solver used: %s multiple_out\n" % solver)


    sk=p.get_strict_knowledge()

    if(sk==False):
        #print "Base de coneixement no consistent"
        p.stats.knowBase=False
        solving_time=time.time()-t1
        print "KB not CONSISTENT"
        f.write("KB not CONSISTENT\n")
        print "Solving time:", solving_time
        f.write("Time: %f\n" % solving_time)
        f.close()
        exit()

    

    max_level= p.get_max_level()
    S=stack()
    S_reasons=stack()
    ext=0
    O=[]
    alpha=0

    S.push(p.get_warranted(),reasonList(),p.get_blocked(),reasonList(),0)
    W_reasons=reasonList()
    for lit in p.get_warranted():
        if lit in W_reasons.keys():
            W_reasons[lit].append(lit)
        else:
            W_reasons[lit]=[[lit]]
    S_reasons.push(W_reasons,reasonList(),reasonList(),reasonList(),0)    

    while not S.is_empty():
        
        W,W_r,B,B_r,alpha=S.pop()
        #W_r,W_re,B_r,B_re,alpha_r=S_reasons.pop()
        print " pop!:::::>traiem %s de la pila" % str((W,B,alpha))
        while alpha <= max_level:
            #c=raw_input("Level %i ... \n(Pila: %s) \n(W=%s,B=%s,alpha=%s)" % (alpha,str(S),str(W),str(B),str(alpha)))
            alpha+=1
            W,W_r,B,B_r,alpha=level_computing(p,ext,O,S,W,W_r,B,B_r,alpha,solver)


    solving_time=time.time()-t1
    print "Outputs:"
    f.write("Outputs:\n")
    Warr=[]
    num_lit_output=0
    print O
    for idx,output in enumerate(O):
        print "output ",idx,":",output
        f.write("output %i: %s\n" % (int(idx)+1,output))
        Warr.append(set(output[0]))
        num_lit_output+=len(output[0])
    print num_lit_output,output[0]
    mean_num_lit_output=float(num_lit_output) / (int(idx)+1)



    print "Number of outputs", int(idx)+1
    f.write("Number of outputs: %i\n" % (int(idx)+1))
    print "Mean literals per number of outputs", mean_num_lit_output
    f.write("Mean literals per number of outputs: %f\n" % mean_num_lit_output)
    print "Intersection:",set.intersection(*Warr), len(set.intersection(*Warr))
    f.write("Intersection: %s %i\n" % (set.intersection(*Warr),len(set.intersection(*Warr))))
    print "Solving time:", solving_time
    f.write("Time: %f\n" % solving_time)

    f.close()
