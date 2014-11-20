#!/bin/python

import sys, re, os
from optparse import OptionParser
import __builtin__
import time

from pdelp import Literal, Clause, Program, not_depend, conflict, rulesCache, almostValidCache, conflictASP, not_dependASP,validLiteralsList
from PySAT import ConjunctiveNormalFormula

SATSOLVERS=["minisat","precosat","glucose"]

def cycle(cycle_iter):
    '''We define a cycle when after an iteration
    the valid literals list does not change'''

    return cycle_iter[0]-cycle_iter[1]>=2

def prev_conflict_check(vc,program):
    '''check if negated literal in initial level
    (W U valids), a conflict must arise'''
    prev_conflict=[]
    for literal in vc:
        #FET!##TODO: modificar a dos comprovacions
        if literal.neg() in vc or literal.neg() in program.get_warranted():
            prev_conflict.append(literal)
    return prev_conflict
            
def level_computing(level, program, unicity, solver):

    #List with valid literals at this level
    #also starts a list with lists with possible rules 
    #with valid literals in further steps
    vc=program.get_valid_literals(level)
    program.almostValidCache=almostValidCache()
    #Dict where literals are set as visited and valid
    vL=validLiteralsList(vc)
    #Literals that for sure will generate a conflict
    conflictiveLiterals=[]
    #Cycle iterator
    cycle_iter=[0,0]

    while vL.none_valid() is False:
        #check for literals which have its negated in W or vc
        conflictiveLiterals=prev_conflict_check(vc,program)
        for literal in conflictiveLiterals:
            vL.unset_valid(literal)
            print "*****",vc,literal
            vc.remove(literal)

        #we add an iteration to the register
        cycle_iter[0]+=1

        #we will iterate vc this way, because it will be dynamically updated
        #all new valid literals will be appended to the end
        #vL.all_visited() is redundant, but it is only an integer comparison
        i=0
        while i<len(vc) and vL.all_visited() is False:
            literal=vc[i]
            print "Check literal ", literal, "in ", vc, "is visited ", \
                vL.is_visited(literal)," is valid ",vL.is_valid(literal), "all visited?",  vL.all_visited()
            if not vL.is_visited(literal) and vL.is_valid(literal):
                notDepend=not_depend(program,level,literal,vc,solver)
                vL.set_visited(literal)
                print "-> Blocked literals:",program.get_blocked(0,level)
                print "+++++++++++++++++++++++++++++++++",conflict(program,level,literal,vc,program.get_warranted(0,level),notDepend,1,solver)
#                c=raw_input("------=========----------")
                confl=conflict(program,level,literal,vc,program.get_warranted(0,level),notDepend,1,solver)
                print "****  Conflict for warrant ?????->>>",confl[0]
                if not cycle(cycle_iter) and \
                        not confl[0]:
                    program.set_warranted(level,literal)
                    print "literal",literal," warranted, list of W", program.get_warranted(0,level)
                    print vc,"AV: ",notDepend,"W: ",program.get_warranted(0,level), "B: ",program.get_blocked(0,level)
                    program.stats.set_warranted(literal,program.rulesList.get_producing_rule2(program,literal),level)
                    print literal, program.rulesList.get_producing_rule(literal)
                    #c=raw_input("    ")
                    vL.unset_valid(literal)
                    vc.pop(i)
                    #update vc   
                    new_vc=program.update_valid_literals(literal,level)
                    for lit in new_vc:
                        if not vL.exists(lit):
                            vL.insert(lit)
                            vc.append(lit)
                    #update last change to actual iteration
                    cycle_iter[1]=cycle_iter[0]
                else:
                    i+=1
            #else:
            #    i+=1
            #c=raw_input("________")
        #FET##TODO: afegir els previous conflicts i els traiem de vc i els posem a I
        I=conflictiveLiterals
        if len(I)>0:
            confl=True
            cycl=False
            c_lit=I
        for literal in vc:
            if vL.is_valid(literal):
                cycl=cycle(cycle_iter)
                if not cycl:
#                    c=raw_input("****************************")
                    var_confl=conflict(program,level,literal,vc,program.get_warranted(0,level),None,2,solver)
                    print "+++++++++++++'''''++++++++++++++++++",var_confl,type(var_confl)
                    confl,c_lit=conflict(program,level,literal,vc,program.get_warranted(0,level),None,2,solver)
                    
                   
                    for lit in c_lit:
                        if lit in program.get_warranted():
                            c_lit.remove(lit)
                    print "*** Conflict for block  de %s ???:::" % literal,confl
                if cycl:
                    print "**** Cicle de ",vc
                    I=I+vc
                    break
                if cycl or confl:
                    if not confl:
                        c_lit="cycle"
                    I.append(literal)
                    cycle_iter[1]=cycle_iter[0]

        for literal in I:
            vL.unset_valid(literal)
            print "#####",vc,literal
            if literal in vc:
                vc.remove(literal)
            print "---> set blocked:", literal, confl, cycl,":",c_lit
            program.set_blocked(level,literal)
            program.almostValidCache.update(literal)
            if cycl:
                #posar als stats bloquejats per cycle
                #program.stats.set_blocked(literal,"cycle",I,level)
                program.stats.prova(program,literal,"cycle",I,program.rulesList.get_producing_rule2(program,literal),level)
            else:
                #program.stats.set_blocked(literal,"conflict",c_lit,level)
                program.stats.prova(program,literal,"conflict",c_lit,program.rulesList.get_producing_rule2(program,literal),level)
                #posar els bloquejats per conflicte
            #c=raw_input("---STOP at blocked---")
            #we set unvalid because it must be checked in next iteration for a cycle
        for lit in vc:
            if vL.is_valid(lit):
                vL.unset_visited(lit)


def solve(p,options):

    __builtin__.DEBUG=False
        
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

        SCRPATH=os.path.realpath(__file__)
        t=re.match('(.*)/RP_DeLPsolver.py',SCRPATH)
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
    stats['warrant_list']=[]
    stats['blocked_list']=[]
    stats['times']=[]
    stats['n_outputs']=1
    stats['consistent']=True
    

    sk=p.get_strict_knowledge()
    print p.clauses, p.get_warranted(0)

    if(sk==False):
        p.stats.knowBase=False
        stats['consistent']=False
        return stats
        
    max_level= p.get_max_level()
    for level in range(1, max_level):
        level_computing(level, p, True, solver)
    t2=time.time()
    
    stats['warrant_list'].append(p.stats.warrant_list)
    stats['blocked_list'].append(p.stats.blocked_list)
    #print "#########",p.stats.blocked_list
    stats['times']=[t2-t1]
    
    return stats


