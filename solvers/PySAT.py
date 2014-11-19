#!/usr/bin/python

import re, sys
import os
import exceptions
import __builtin__
import random
from sympy.logic.algorithms.dpll import *
#import RP_DeLPsolver
import subprocess


def unit_prop_int_repr(clauses, symbols, model):
    """
Compute satisfiability in a partial model.
Arguments are expected to be in integer representation

>>> from sympy.logic.algorithms.dpll import dpll_int_repr
>>> dpll_int_repr([set([1]), set([2]), set([3])], set([1, 2]), {3: False})
False

"""
    # compute DP kernel
    #print clauses
    P, value = find_unit_clause_int_repr(clauses, model)
    while P:
        model.update({P: value})
        symbols.remove(P)
        if not value:
            P = -P
        clauses = unit_propagate_int_repr(clauses, P)
        P, value = find_unit_clause_int_repr(clauses, model)
    P, value = find_pure_symbol_int_repr(symbols, clauses)
    # end DP kernel
    unknown_clauses = []
    for c in clauses:
        val = pl_true_int_repr(c, model)
        if val is False:
            return False
        if val is not True:
            unknown_clauses.append(c)
    return model

class ConjunctiveNormalFormula:

    def __init__(self,*args):
        self.fil=ENCODINGPATH+"/"+self.__getFilename__(args[0])         
        self.nv=1
        self.vars=[]
        self.clauses=[]
        self.encoding=[]
        self.mapa_assignacions=[]

    def push(self, clause):
        if(isinstance(clause,list)):
            for var in clause:
                self.push(var)
        else:
            newClause=""
            m=re.findall("(-*~*\w+)",clause)
            if(m):
                for newVar in m:
                    if(newVar[0]=="-"):newVar=newVar[1:]
                    try: 
                        self.vars.index(newVar)
                    except ValueError: 
                        self.vars.append(newVar)
                        self.nv+=1
                self.clauses.append(m)
            else:
                return

    def push_beta(self, clause):
        if(isinstance(clause,list)):
            for cl in clause:
                self.push_beta(cl)
        else:
            clause=Clause(clause)
            #discard empty clauses
            if(len(clause.clause)==0): return
            for new_var in clause.variables:
            #Are regular expressions a better choice?
                if(new_var[0]=="~"): new_var=new_var[1:]
                try: 
                    self.vars.index(new_var)
                except ValueError: 
                    self.vars.append(new_var)
                    self.nv+=1
                else:
                    pass
            self.clauses.append(clause.clause)
        
    def show(self):
        for clause in self.clauses:
            print clause
        print "Vars:",self.vars

    def varNumber(self):
        return len(self.vars)

    def clauseNumber(self):
        return len(self.clauses)

    def write(self, method):
        if(method=="minisat" or method=="modminisat" or method=="precosat" or method=="glucose"):
            output="p cnf %i %i \n" % (self.varNumber(),self.clauseNumber())
            for clause in self.clauses:
                if(clause[0]=="*"):
                    output=output+"c"+str(clause[1:])+"\n"
                else:
                    for var in clause:
                        #Let's accept both negation symbols - and ~ for an ease of encoding
                        #Also, delete double negations
                        if(var[0]=="-"):
                            value=-(self.vars.index(var[1:]))-1
                        else:
                            value=self.vars.index(var)+1
                        output=output+str(value)+" "
                    output=output+"0\n"
        else:
            output="c PySAT Error: unavailable method\n"+"0"
        f=open(self.fil,"w")
        f.write(output)
        f.close()

    def unitPropagation(self):
        clauses_int_repr=[]
        for clause in self.clauses:
            if(clause[0]=="*"):
                pass
            else:
                cla=[]
                for var in clause:
                        #Let's accept both negation symbols - and ~ for an ease of encoding
                        #Also, delete double negations
                    if(var[0]=="-"):
                        value=-(self.vars.index(var[1:]))-1
                    else:
                        value=self.vars.index(var)+1
                    cla.append(value)
                #modificacio del nou sympy, han de ser sets enlloc de lists
                clauses_int_repr.append(set(cla))
        symbols_int_repr=set(range(1, len(self.vars) + 1))
        result=unit_prop_int_repr(clauses_int_repr, symbols_int_repr, {})

        output=[]
        if(result != False):
            for value in result:
                if result[value]:
                    output.append(self.vars[value-1])
                elif not result[value]:
                    output.append("-"+self.vars[value-1])
            return output
        else:
            return False

    def setFilename(self, fil):
        self.fil=__getFilename__(self,fil)
        
    def __getFilename__(self, f):

        c=re.match("(.*/)*(.*)$",f)
        if(c.group(1)):
            filepath=c.group(1)
        else:
            filepath="./"
        filename=c.group(2)

        return filename
        filelist=" ".join(os.listdir(filepath))       
        index=0

        for match in re.findall("(%s(?:-[0-9]*)*)" % filename,filelist):
                c=re.match("(?:%s-([0-9]*))" % filename, match)
                if(c):
                    if(index<=int(c.group(1))):
                        index=int(c.group(1))+1
                        
        if(index==0):
            return "%s-1" % (f)
        else:
            return "%s-%i" % (f,index)

    def comment(self, string):
        '''
        Inserts a comment in the encoding. When writting, we will check if "*"
        is the first char to appear.
        '''
        string="* "+string
        self.clauses.append(string)
    
    def solve(self, method):
        #s'ahuria de fer tot amb subprocess
        sol_out = []
        self.write(method)
        if(method=="minisat"):
            #cmd="%s/minisat %s %s.sol &>/dev/null" % (MINISATPATH,self.fil,self.fil)
            args=[MINISATPATH+"minisat", self.fil, self.fil+".sol"]
            msolve=subprocess.Popen(args, shell=False, stderr=subprocess.PIPE,stdout=subprocess.PIPE)
            msolve.wait()
            stdout_value = msolve.communicate()[0]
        elif(method=="modminisat"):
            cmd="%s/minisat %s %s.sol &>/dev/null"  % (MODMINISATPATH,self.fil,self.fil)
        elif(method=="precosat"):
            sol=[]
            sol.append("")
            sol.append("")
            cmd="%s/precosat %s > %s.sol"  % (PRECOSATPATH,self.fil,self.fil)
            solFile=os.system(cmd)
            f = open("%s.sol" % self.fil ,"r")
            solFile=f.readlines()
            if(len(solFile)==0):
                raise Exception("Bad sol file for precosat solver")
            g=re.match("^s (.*)ISFIABLE\n$",solFile[0])
            if(g):
                sol[0]=re.sub("^s (.*)\n", "%s" % g.group(1),solFile[0])
            else:
                raise Exception("Bad sol file for precosat solver")
            for i in range(1, len(solFile)):
                h=re.match("v (.*)\n$",solFile[i])
                if(h):
                    sol[1]=sol[1]+re.sub("^v (.*)\n","%s" % h.group(1), solFile[i])+" "                
            f.close()

        elif method=="glucose":
            args=[GLUCOSEPATH+"glucose", self.fil, self.fil+".sol"]
            pb_trans=subprocess.Popen(args, shell=False, stderr=subprocess.PIPE,stdout=subprocess.PIPE)
            pb_trans.wait()
            stdout_value = pb_trans.communicate()[0]
            #print repr(stdout_value)


        #aixo s'haura dir millorar
        #if(method=="minisat" or method=="modminisat"):
        if(method=="modminisat"):
            sol=os.system(cmd)
            f = open("%s.sol" % self.fil ,"r")
            sol=f.readlines()
            f.close()

        elif method=="glucose" or "minisat":
            f = open("%s.sol" % self.fil ,"r")
            sol=f.readlines()
            f.close()
        

        if(sol[0]=="UNSAT\n" or sol[0]=="UNSAT"):
            #print "UNSATISFIABLE"
            #os.system("rm %s" % self.fil)
            #os.system("rm %s.sol" % self.fil)
            return ["UNSAT",[]]
        else:
            sol=sol[1].split(" ")

        for idx in sol:
            if(idx!="0\n" and idx!="0"):
                try:
                    if(idx[0]=="-"): symb="-"
                    else: symb=""
                    sol_out.append(symb+self.vars[abs(int(idx))-1])
                except ValueError:
                    pass
                except IndexError:
                    pass
                
        if(DEBUG):
            f_debug=open(self.fil+".debug","w")
            debug_out="\n\n"
            debug_out=debug_out+"======================\n"
            debug_out=debug_out+"|Variable assignement|\n"
            debug_out=debug_out+"======================\n"
            debug_out=debug_out+"|  VarEnc |  VarSolv |\n"
            debug_out=debug_out+"======================\n"
            for idx,var in enumerate(sol_out):
                if(var[0]=="-"): val="-"+str(idx+1)
                else: val=str(idx+1)
                debug_out=debug_out+ "|    "+var+"    |    "+val+"     |\n"
            debug_out=debug_out+"======================\n"
            f_debug.write(debug_out)
            f_debug.close()
            #print debug_out
        #os.system("rm %s" % self.fil)
        #os.system("rm %s.sol" % self.fil)
        if(DEBUG):
            os.system("rm %s.debug" % self.fil)
        return ["SAT",sol_out]

    def __str__(self):
        outStr=""
        for clause in self.clauses:
            for var in clause:
                outStr=outStr+var+" "
            outStr=outStr+"\n"
        return outStr

class Clause(object):
    def __init__(self, *args):
        #So we can use integers as input variables
        if(len(args)>1):
            raise ValueError, 'too many arguments'
        self.variables=[]
        self.clause=[]
        self.T=False
        if(len(args)==1):
            string=str(args[0])
            if(string[0]=="*"):
                self.comment(string[1:])
            else:
                for var in string.split(" "):
                    if(not(self.is_T())):
                        self.add(var)

    def add(self, string):
        string=str(string)
        for var in string.split(" "):
            #m=re.match("-([a-z]*)|([a-z]*)|-(\d)*|(\d)*",var)
            m=re.search('^(--)*-([a-z0-9]*$)',var)
            if(m==None):
                m=re.search('^-*([a-z0-9]*$)',var)
                var=m.group(1)
            else:
                var="-"+m.group(2)
            
            #We check if its a negated literal, maybe the procedure here is quite weird,
            #then acces to key's value (remember that the key is the atom, it doesn't matter if it is
            #negated -> the value will (or MUST) be
            #It checks for redundancy and tautology, if tautology is infered, then self.T=true and the clause is
            #"blocked" -> there's nothing you can do with it
            if(self.has_var(var)):
                pass
            elif(self.has_negvar(var)):
                self.clause=[]
                self.T=True
            else:
                if(var[0]=="-"):
                    self.variables.append(var[1:])
                else:
                    self.variables.append(var)
                self.clause.append(var)
    def is_T(self):
        return self.T

    def has_var(self, var):
        try:
            self.clause.index(var)
        except ValueError: return False
        return True

    def has_negvar(self, var):
        if(var[0]=="-"):
            return self.has_var(var[1:])
        else:
            return self.has_var("-"+var)
        
    def show(self):
        print self.clause


def incr_numvar(NumVar,pos):
    if(pos>0):
        if(NumVar[pos]>121):
            NumVar[pos]=97
            return incr_numvar(NumVar,pos-1)
        else:
            NumVar[pos] += 1
            return NumVar
    else:
        if(NumVar[pos]>121):
            NumVar[pos]=97
            NumVar.append(97)
            return NumVar
        else:
            NumVar[pos] += 1
            return NumVar

class variable:
    def __init__(self, *args):
        if(len(args)==0):
            init_val=1
        else:
            init_val=args[0]
        self.len=0
        symb=""
        for el in incr_numvar(NumVar,len(NumVar)-1):
            symb=symb+chr(el)
        self.symb=symb


        self.array=[]
        self.add(init_val)

    def __getitem__(self,i):
        return self.array[i]

    def __str__(self):
        return "%s" % self.array

    def __len__(self):
        return len(self.array)

    def add(self, *args):
        if(len(args)==0):
            times=1
        else:
            times=abs(args[0])
    
        for i in range(0,times):
            self.array.append(self.symb+str(self.len))
            self.len+=1



if __name__ == '__main__':
    ENCODINGPATH="/home/francesc/doctorat/solver-RPDeLP/"
    GLUCOSEPATH="/usr/local/bin/"
    MINISATPATH="/usr/bin/"
    DEBUG=True
    cnf=ConjunctiveNormalFormula("prova1")
    cnf.push_beta("1 2 3")
    cnf.push_beta("4 5 6")
    #print cnf.solve("minisat")
    print cnf.solve("glucose")
