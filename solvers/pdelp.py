#!/usr/bin/python
from PySAT import *
import PyASP
import re
import os, time, math
import __builtin__
from xml.etree.ElementTree import Element, SubElement, Comment, tostring, parse

numVars=1
numEnc=1
PERP="Perp"

def dummy_proc(a):

    return a

class stack(list):
    def push(self,W,B,alpha):
        self.insert(0,(W,B,alpha))

class metaRule(list):

    def __init__(self,rule,W,B):
        if isinstance(rule,Clause):
            self.insert(0,rule)
            self.insert(1,[len(rule.getBody()),self.warr_in_body(W),self.has_blocked(B)])

        else:
            raise Exception

    def has_blocked(self,B):
        if self[0].getBody() is not None:
            return len(set(self[0].getBody()).intersection(set(B)))!=0
                
    def warr_in_body(self,W):
        if self[0].getBody() is not None:
            return len(set(self[0].getBody()).intersection(set(W)))

    def condition_v3(self,W,B):
        ''' condition v3 of valid argument'''
        return self[0].getHead() not in W \
            and self[0].getHead() not in B \
            and self[0].getHead().neg() not in B

class inverseList(dict):
    
    def insert(self,rule,c):
        for lit in rule.getBody():
            if lit in self.keys():
                self[lit].append(c)
            else:
                self[lit]=[c]

class rulesList(object):

    def __init__(self):
        self.list=[]
        self.W=[]
        self.B=[]
        self.inv_list=inverseList()
        self.head_list={}
        #to know which levels are in the list
        self.level=-1

    def insert(self,clause,W,B):
        
        if type(clause) is list:
            for c in clause:
                self.list.insert(c,W,B)
        elif isinstance(clause,metaRule):
            if clause.condition_v3(W,B) and clause.has_blocked(B) is False:
                self.list.append(clause)
                c=clause[0]
                self.inv_list.insert(c,clause)
                if c[0] in self.head_list.keys():
                    self.head_list[c[0]].append(clause)
                else:
                    self.head_list[c[0]]=[clause]

    def update_W(self,w):

        vc=[]
        if w in self.inv_list.keys(): 
            for rule in self.inv_list[w]:
                rule[1][1]+=1
                if rule[1][1]==rule[1][0] and rule[1][2] is False:
                    vc.append(rule[0])
        return vc

    def update_B(self,b):
 
        if b in self.inv_list.keys():
            for rule in self.inv_list[b]:
                rule[1][2]=True

    def get_prevalids(self,p,level):
        ''' this method stores in a list
        possible future clause to be valid
        and returns possible actual valids
        ATENTION: conflict generation must be checked'''

        prevalids=[]
        if self.level<level:
            for l in p.clauses[p.rulesList.level+1:level+1]:
                for clause in l:
                    if clause.getBody() is not None:
                        #check rule
                        c=metaRule(clause,p.get_warranted(0,level),p.get_blocked(0,level))
                        p.rulesList.insert(c,p.get_warranted(0,level),p.get_blocked(0,level))
                        if is_prevalid(clause,p.get_warranted(0,level),p.get_blocked(0,level)):
                            prevalids.append(clause.getHead())
                    else:
                        if is_prevalid(clause.getHead(),p.get_warranted(0,level),p.get_blocked(0,level)):
                            prevalids.append(clause.getHead())
                        
            p.rulesList.level=level
        return prevalids

    def get_producing_rule(self,l):
        rules=[]
        if l in self.head_list.keys():
            for mrule in self.head_list[l]:
                if mrule[1][0] == mrule[1][1]:
                    rules.append(mrule[0][1])
        else:
            rules=[l]
        return rules

    def get_producing_rule2(self,p,l):
        rules=[]
    	for level in p.clauses:
	    for rule in level:
	       	if rule[0] == l:
                    #print "si"
	            if len(rule)>1:
	                rules.append(rule[1])
		    else:
                        #print "ok!"
		        rules.append(rule[0])
        return rules


def is_prevalid(l,W,B):
    if isinstance(l,Literal):
        return l not in W \
            and l not in B \
            and l.neg() not in B
    if isinstance(l,Clause):
        if is_prevalid(l.getHead(),W,B):
            return l.getBody() not in B and set(l.getBody()).issubset(set(W))
    elif isinstance(l,str):
        return is_prevalid(Literal(l),W,B)

class stats():
    def __init__(self):
        self.almostValidCalls=0
        self.conflict1Calls=0
        self.conflict2Calls=0
        self.t1=time.time()
        self.knowBase=True
        self.warrant_list=[]
        self.blocked_list=[]
        self.solver=""
        self.file_solved=""
        self.comments=""

    def __str__(self):
        kbstat=""
        warr=""
        block=""
        if not self.knowBase:
            kbstat="KB not CONSISTENT\n"
        for lit in self.warrant_list:
            warr=warr+str(lit)+"\n"
        for lit in self.blocked_list:
            block=block+str(lit)+"\n"
        stat="\n\n===============\n    STATS\n===============\n"+kbstat+\
            "Warranted literals:\n"+warr+"\n"\
            "Blocked literals:\n"+block+"\n"\
            "Almost valid calls: "+str(self.almostValidCalls)+"\n"\
            "Conflict 1 calls: "+str(self.conflict1Calls)+"\n"\
            "Conflict 2 calls: "+str(self.conflict2Calls)+"\n"\
            "Time: "+str(time.time()-self.t1)+" seconds"
        return stat
        #return ""

    def set_warranted(self,lit,rule,level):
        self.warrant_list.append((lit,rule,level))

    def set_blocked(self,lit,block_reason,blit,level):
        self.blocked_list.append((lit,block_reason,blit,level))

    def prova(self,p,lit,block_reason,blit,prod_rule,level):

        self.blocked_list.append((lit,block_reason,blit,prod_rule,level))            
        #c=raw_input("***********_________%s___________*****************" % rul)

        

class rulesCache():
    def __init__(self):
        self.rules=[]
        #segurament esta malament i es pot accedir al objecte de nivell superior. ni idea de POO
        self.warrLit=set()
        
    def addRule(self, rule):
        if(rule.body):
            if(set(rule.body).difference(self.warrLit)==0):
                return (rule.head,rule)
            else:
                self.rules.append(rule)

    def updateWarranted(self, literal):
        output=[]
        self.warrLit.add(literal)
        ##print self.warrLit
        for rule in self.rules:
            if literal in rule.body:
                ##print literal, set(rule.body), self.warrLit, set(rule.body).difference(self.warrLit)
                if(len(set(rule.body) - self.warrLit) == 0):
                    ##print literal, rule.body
                    output.append(rule)
                    self.rules.remove(rule)
        return output

class validLiteralsList(object):

    def __init__(self,vc):
        self.list={}
        self.length=0
        self.visited=0
        self.valid=self.length
        self.insert(vc)
        

    def insert(self,lit):
        if type(lit) is list:
            for l in lit:
                self.insert(l)
        else:
            if not self.exists(lit):
                self.list[lit]=[True,False]
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

class almostValidCache(object):
#'''It holds a list of almost valid arguments for a tuple (P,Q)'''
 
    def __init__(self):
        self.queries={}
        self.p_lit={}

    def insert(self,p,q,lit_list,b_val):
        #insertem la resposta de la query
        if q in self.queries.keys():
            self.queries[q][p]=b_val
        else:
            self.queries[q]={p:b_val}

        #guardem el literal que produeix q per si es bloqueja o garanteix
        for el in lit_list:
            if el in self.p_lit.keys():
                self.p_lit[el].append(q)
            else:
                self.p_lit[el]=[q]

    def check(self,p,q):
        if q in self.queries.keys():
            if p in self.queries[q].keys():
                return self.queries[q][p]
        else:
            return None

    def update(self, b_lit):
        self.clear(b_lit)
        #print b_lit, self.p_lit.keys(),  b_lit in self.p_lit.keys()
        if b_lit in self.p_lit.keys():
            for lit in self.p_lit[b_lit]:
                self.clear(lit)

    def clear(self,target_lit):
        #print "clearing........  ",target_lit
        if target_lit in self.queries.keys():
            #print "         deleting.... ", self.queries[target_lit]
            del self.queries[target_lit]
        for lit in self.queries.keys():
            if target_lit in self.queries[lit].keys():
                #print "         deleting.... ", self.queries[lit][target_lit]
                del self.queries[lit][target_lit]
              
class Literal(str):
    def __new__(cls, arg):
        m=re.match("^(~~)*(\w+)$|^(~)*~(\w+)$",arg)
        if(m):
            lit = super(Literal,cls).__new__(cls,re.sub("(~~)*","",arg))
            return lit
        
        else:
            raise Exception('Not a valid syntax for Literal')
        
    def neg(self):
        return Literal("~"+self)

    def abs(self):
        if self[0]=="~":
            return self[1:]
        else:
            return self

    def cnf(self,*args):
        if(len(args)>1):
            raise Exception
        elif(len(args)<1):
            return self
        else:
            if(args[0]==0): 
                return "-"+self

class Clause(list):    
    def __init__(self,*args):
        if(len(args)==0):
            self.insert(0,"")
            self.insert(1,[])
        elif(len(args)==1):
            if(type(args[0])==tuple):
                self.setHead(args[0][0])
                if(len(args[0])>1):
                    self.setBody(args[0][1])
            else:
                m=re.match("\s*(~*\w+)\s*:-(?:\s*(~*\w+)\s*)*|\s*(~*\w+)\s*",args[0])
                if(m):
                    m=re.findall("(~*\w+)",args[0])
                    self.head=m[0]
                    if(len(m)>1):
                        self.body=m[1:]
                else:
                    raise Exception("Bad Clause syntaxis")
        else:
            raise TypeError
    def setHead(self, head):
        self.insert(0,Literal(head))

    def getHead(self):
        try: return self[0]
        except: return None

    def setBody(self, body):
        try:self[1]
        except IndexError:
            self.insert(1,[])
        if(isinstance(body,list) or isinstance(body,tuple)):
            for lit in body:
                self[1].append(Literal(lit))
        if(isinstance(body,str)):
            self[1].append(Literal(body))

    def delBody(self, body):
        if body in self[1]:
            self[1].remove(body)

    def getBody(self):
        try:return self[1]
        except IndexError:
            return None
    
    def asCnf(self):
        cnf=str(self.head.cnf())
        if(self.body):
            for lit in self.body:
                cnf=cnf+" "+lit.cnf(0)
        return cnf


    head=property(getHead,setHead)
    body=property(getBody, setBody, delBody)
    
class mystr(str):

    def __init__(self,a):
        self.append(a)

class Program(object):
    def __init__(self, fileIn):
        self.clauses=[]
        self.warranted=[]
        self.blocked=[]
        self.__headIndex__=[]
        self.__bodyIndex__=[]
        self.rulesCache=rulesCache()
        self.rulesList=rulesList()
        self.almostValidCache=almostValidCache()
        #self.producingRules={}
        self.stats=stats()
        self.fileName=fileIn

        t = re.compile('.*\.xml$')
        if t.match(fileIn):
            lvls=[]
            root=parse(fileIn)
            sk=root.find("strict_level")
            lvls.append([])
            def_levels={}

            for clause in sk.findall('clause'):
                lvls[0].append(clause.text)

            for level in root.findall('defeasible_level'):
                alpha=level.attrib['alpha']
                clauses=[]
                for clause in level:
                    clauses.append(clause.text)
                def_levels[alpha]=clauses
            
            for level in sorted(def_levels.keys()):
                lvls.append(def_levels[level])

            for idx,level in enumerate(lvls):
                for clause in level:
                    line=re.sub("\.\s$","",clause)
                    self.add_clause(Clause(line),idx)
                    
            #self.inverseList=inverseRulesList(self.clauses)
        else:
            #print "Loads a file and parses its lines"
            program=open(fileIn,"r")
            for line in program.readlines():
                if(re.search("^:strict.*",line)):
                    level=0
                    self.clauses.insert(level,[])
                    self.blocked.insert(level,[])
                    self.warranted.insert(level,[])
                elif(re.search("^:defeasible.*",line)):
                    level += 1
                    self.clauses.insert(level,[])
                    self.blocked.insert(level,[])
                    self.warranted.insert(level,[])
                elif(re.search("^:end.*",line)):
                    break
                else:
                    if(re.match("\s*~*\w(.*)(\.)\s$",line)):
                        line=re.sub("\.\s$","",line)
                        self.add_clause(Clause(line),level)
                        #print line, level
                        #print self.clauses
                    #raise Exception("Invalid syntax for a P-DeLP program")

    def set_warranted(self,level,clauses):
        '''Sets a literal warranted at level level'''
        if(isinstance(clauses,str)):
            try: self.warranted[level].append(Literal(clauses))
            except IndexError:
                self.warranted.insert(level,[Literal(clauses)])
        elif(isinstance(clauses,list)):
            for clause in clauses:
                self.set_warranted(level,clause)

    def get_strict_knowledge(self):
        '''Obtains warranted knowledge at strict level'''
        global numEnc
        ##print "=|>Getting strict knowledge "+str(numEnc)
        cnf=ConjunctiveNormalFormula("%s-%i" % (self.fileName,numEnc))
        numEnc=numEnc+1
        

        if len(self.clauses[0])<1:
            return True

        for clause in self.clauses[0]:
            cnf.push(clause.asCnf())
            cnf.push("-"+clause.head+" -"+clause.head.neg())
        
        result=cnf.unitPropagation()
        
        if(result != False):
            if(result):
                for var in result:
                    if(var[0]!="-"):
                        self.set_warranted(0,var)
                        self.stats.set_warranted(var,self.rulesList.get_producing_rule(var),0)
            return True
        else:
            return False

    def get_warranted(self,*params):

        '''
        Returns warranted literals accepting:
        1: no parameters-> all warranted literals
        2: one parameter-> warranted literals at level params[0]
        3: two parameters-> warranted literals from level params[0] to params[1]
        '''

        war=[]
        if(not params):
            return self.get_warranted(0,len(self.warranted))
        elif(len(params)==1):
            try:
                return self.warranted[params[0]]
            except IndexError:
                return []
        else:
            for level in self.warranted[params[0]:params[1]+1]:
                war.extend(level)
        return war

    def set_blocked(self,level,clauses):
        '''
        Set clauses to blocked. It can be a string or a list
        '''
        if(isinstance(clauses,str)):
            try: self.blocked[level].append(Literal(clauses))
            except IndexError:
                self.blocked.insert(level,[Literal(clauses)])
        elif(isinstance(clauses,list)):
            for clause in clauses:
                try: self.blocked[level].append(Literal(clause))
                except IndexError:
                    self.blocked.insert(level,[Literal(clause)])

    def get_blocked(self,*params):
        '''
        Return blocked literals for a level (params[0]) or an interval (params[0]-params[1])
        '''
        block=[]
        if(not params):
            return self.get_blocked(0,len(self.blocked))
        elif(len(params)==1):
            return self.blocked[params[0]]
        else:
            for level in self.blocked[params[0]:params[1]+1]:
                block.extend(level)
            return block

    def update_valid_literals(self,l,level):

        if l in self.get_warranted(0,level):
            vc_rules=self.rulesList.update_W(l)
            return [lit[0] for lit in vc_rules if \
                        (is_prevalid(lit[0],self.get_warranted(0,level),self.get_blocked(0,level)) \
                             and not self.generates_conflict(lit[0],level))]
        elif l in self.blocked:
            self.rulesList.update_B(l)

    def add_clause(self, clause, level):

        if len(self.__headIndex__)>=level+1:
            #print "1",clause, level
            self.clauses[level].append(clause)
            self.__addIndexes__(clause,level)
        else:
            #print "2",clause, level
            self.clauses.insert(level,[])
            self.__headIndex__.insert(level,{})
            self.__bodyIndex__.insert(level,{})
            self.add_clause(clause, level)

#        try:
#            #self.clauses[level].append(clause)
#            #print "1",clause, level,len(self.__headIndex__)
#            self.__addIndexes__(clause,level)
#        except IndexError:
#            #print "2",clause, level
#            self.clauses.insert(level,[])
#            self.__headIndex__.insert(level,{})
#            self.__bodyIndex__.insert(level,{})
#            self.add_clause(clause, level)

    def add_clause2(self, clause, level):
        try:
            self.__addIndexes__(clause,level)
            if(clause.body):          
                if( len(set(clause.body)-set(self.get_warranted()))!=0 and len(set(clause.body).intersection(self.get_blocked()))==0):
                    #self.rulesCache.addRule(clause)
                    pass
        except IndexError:
            self.clauses.insert(level,[])
            self.__headIndex__.insert(level,{})
            self.__bodyIndex__.insert(level,{})
            self.add_clause(clause, level)

    def get_max_level(self):
        return len(self.clauses)

    def __addIndexes__(self,cla,level):  
        '''
        It adds a new clause to the program, and also adds the body
        to bodies dictionary (for a fast access to bodies by heads. And also
        to heads dictionary (for a fast access to heads by bodies).
        '''
        
        
        if not cla.body:
            #if a fact (head with no body)
            body=None

        else:
            body=cla.body
            #print cla.body
            for literal in body:
                if literal in self.__bodyIndex__[level]:
                #remember bodies dictionary has a list with its heads
                    #print self.__bodyIndex__[level]
                    self.__bodyIndex__[level][literal].append(cla.head)
                else:
                    self.__bodyIndex__[level][literal]=[Literal(cla.head)]
            if cla.head in self.__headIndex__[level]:
            #remember heads dictionary has a list with its bodies
                self.__headIndex__[level][cla.head].append(list(body))
            else:
                self.__headIndex__[level][cla.head]=[list(body)]


    def getHeadByBody(self,level,literal):
        '''
        Returns heads for a given body if exists, if not None is returned
        '''
        #TODO un bodie podria activar diversos heads
        try: return self.__bodyIndex__[level][literal]
        except: return None

    def getBodyByHead(self,level,literal):
        '''
        Returns bodies for a given head if exists, if not None is returned
        '''
        #TODO hauria de retornar una llista de tuples ja que un head pot activar diversos bodies
        if(level<0): return None
        try: 
            return self.__headIndex__[level][literal]
        except: return self.getBodyByHead(level-1,literal)

    def generates_conflict(self, literal, l):
        '''Check if literal l generates conflict with strict knowledge plus
        warranted literals
        Warning: As long as negated literals are used as dual literals, we add the following implication
        for every rule head and warranted literal literal -> -(~literal)
        We should check if it is inefficient'''
        #global numEnc
        ##print "=|>Encoding Generates Conflict "+str(numEnc)
        ##print "=|>"+literal
        cnf=ConjunctiveNormalFormula("%s-%i" % (self.fileName,numEnc))
        #numEnc=numEnc+1
        for rule in self.clauses[0]:
            cnf.push(rule.asCnf())
            cnf.push("-"+rule.head+" -"+rule.head.neg())
            #cnf.push(rule.head+" "+rule.head.neg())
        for warrLiteral in self.get_warranted(0,l):
            cnf.push(warrLiteral.cnf())
            cnf.push("-"+warrLiteral+" -"+warrLiteral.neg()) 
        cnf.push(Literal(literal).cnf())
        
        result=cnf.unitPropagation()
        
        if(not result):
            ##print "           no", result
            return True
        else:
            ##print "           yes", result
            return False

    def get_valid_literals(self,level):
        '''this procedure will be done each time a
        new level procedure is called. so it loads
        rules i rulesList and returns initial valid literals'''
        vc=[]
        pre_vc=self.rulesList.get_prevalids(self,level)
        #check if new literals generates conflict
        for literal in pre_vc:
            if not self.generates_conflict(literal,level) and literal not in vc:
                vc.append(literal)
        #if no conflict return
        return vc

    def getValidLiterals(self,l,vc):      
        #modificacio 4-2-2013
        #si ja esta en vc, no cal tornar a comprovar
        vLiteral=vc
        for level in range(0,l+1):
            for rule in self.clauses[level]:
                ##print "###Checking if %s is valid" % rule.head
                if(rule.head not in vLiteral):
                    if(rule.body):
                        if(set(rule.body).issubset(self.get_warranted(0,l))):
                            if((rule.head not in set(self.get_warranted(0,l)).union(self.get_blocked(0,l)))
                                       and (rule.head.neg() not in self.get_blocked(0,l))):
                                if(not self.generates_conflict(rule.head,l)):
                                    vLiteral.append(rule.head)
                    else:
                        if((rule.head not in set(self.get_warranted(0,l)).union(self.get_blocked(0,l)))
                           and (rule.head.neg() not in self.get_blocked(0,l))):
                            if(not self.generates_conflict(rule.head,l)):
                                vLiteral.append(rule.head)
        return vLiteral

    def get_new_valid_literals(self,l,vc):
        vLiteral=vc
        newvLiteral=[]
        for level in range(0,l+1):
            for rule in self.clauses[level]:
#                #print "###Checking if %s is valid" % rule.head
                if rule.head not in newvLiteral and rule.head not in vLiteral:
                    if rule.body :
                        if set(rule.body).issubset(self.get_warranted(0,l)):
                            if((rule.head not in set(self.get_warranted(0,l)).union(self.get_blocked(0,l)))
                                       and (rule.head.neg() not in self.get_blocked(0,l))):
                                if(not self.generatesConflict(rule.head,l)):
                                    vLiteral.append(rule.head)
#                                    #print True
                    else:
                        if((rule.head not in set(self.get_warranted(0,l)).union(self.get_blocked(0,l)))
                           and (rule.head.neg() not in self.get_blocked(0,l))):
                            if(not self.generatesConflict(rule.head,l)):
                                vLiteral.append(rule.head)
#                                #print True
        return newvLiteral
    

    def getStrictRules(self):

        return [rule for rule in self.clauses[0] if len(rule)>1]
    
    

    def getAlphaRules(self, level):
        arules=[]
        for l in range(0,level+1):
            for clause in self.clauses[l]:
                ##print clause
                if(clause.body):
                    #new a-rule definition
                    if((set(clause.body).difference(set(self.get_warranted(0,level))) and l<level) or l>=level):
                        if(not set(clause.body).intersection(set(self.get_blocked(0,level)))):
                            if(clause.head not in set((set(self.get_warranted(0,level))).union(set(self.get_blocked(0,level)))) and clause.head.neg() 
                               not in set((set(self.get_warranted(0,level))).union(set(self.get_blocked(0,level))))):
                                arules.append(clause)
        return arules

    def is_active_rule(self,rule,level):
        for lit in rule:
            if lit not in self.get_warranted(level):
                return False
        return True

    def __str__(self):
        outStr=""
        for idx,level in enumerate(self.clauses):
            outStr=outStr+"Level: "+str(idx)+"\n"
            for clause in level:
                outStr=outStr+clause.head
                if(clause.body):
                    outStr=outStr+" :-"
                    for literal in clause.body:
                        outStr=outStr+" "+literal
                outStr=outStr+"\n"
        return outStr

    #cnf=ConjunctiveNormalFormula()



def not_depend(program,level,Q,vc,solver):
    setOfConclusions=[]
    for clause in program.clauses[level]:
        if clause[0] not in vc and  clause[0] not in setOfConclusions:
            if solver=="minisat" or solver=="glucose":
                if almost_validSAT(program,Q,clause[0],vc,level,solver):
                    setOfConclusions.append(clause[0])
            elif solver=="clingo":
                almost_validASP(program,Q,clause[0],vc,level)
                if almost_validASP(program,Q,clause[0],vc,level):
                    setOfConclusions.append(clause[0])

    return setOfConclusions

def not_dependSAT(program,level,Q,vc,method):
    #vc=program.getValidLiterals(level,vc)
    setOfConclusions=[]
    for clause in program.clauses[level]:
        if clause[0] not in vc+setOfConclusions:
            if(almost_validSAT(program,Q,clause[0],vc,level,method)):
#                #print clause[0]," is not dependent of ",Q
                setOfConclusions.append(clause[0])
            else:
                ##print clause[0]," is dependent of ",Q
                pass

    return setOfConclusions

def not_dependASP(program,level,Q,vc):

    vc=program.getValidLiterals(level,vc)
    setOfConclusions=[]
    for clause in program.clauses[level]:
        if clause[0] not in vc+setOfConclusions:
            if(almost_validASP(program,Q,clause[0],vc,level)):
                ##print clause[0]," is not dependent of ",Q
                setOfConclusions.append(clause[0])
            else:
                ##print clause[0]," is dependent of ",Q
                pass
    return setOfConclusions
            


class myDict(dict):
    def pushitem(self,key):
        global numVars
        self[key]=str(numVars)
        numVars=numVars+1
    def findKey(self, val):
        '''
        return the key of dictionary dic given the value
        '''
        return [k for k, v in self.iteritems() if v == val]

class myList(list):
    def __init__(self):
        global numVars

    def Var(self, i, x,*args):
        l=0
        nVar=0
        if(args):
            nVar=int(args[0])
        for j in range(0,i):
            l=l+len(self[j])
        try:
            return self[i].index(x)+l+1+nVar
        except ValueError:
            return None

    def getVar(self,i,*args): 
        nVar=1
        if(args):
            nVar=int(args[0])
            return self.getVar(i-nVar)

        for j in range(0,len(self)):
            if(len(self[j])>=i):
                try: return self[j][i-1]
                except IndexError:
                    return None
            else:
                i=i-len(self[j])
    def varLen(self):
        l=0
        for level in self:
            l=len(level)+l
        return l


def conflict(program,level,Q,validLiterals,warLiterals,D,call,solver):
    if solver=="glucose" or solver=="minisat":
        #print Q,"----","AV: ",D,"V: ",validLiterals,"W: ",warLiterals
        #c=raw_input("---Valid and Warr---")
        return conflictSAT(program,level,Q,validLiterals,warLiterals,D,call)
    elif solver=="clingo":
        var_conflict=conflictASP(program,level,Q,validLiterals,warLiterals,D,call)
        #conflictASP(program,level,Q,validLiterals,warLiterals,D,call)
#        c=raw_input("####VAR CONFLICT#### %s #########" % str(var_conflict))
        return var_conflict


def conflictSAT(program,level,Q,validLiterals,warLiterals,D,call):
    global numEnc
    enctim1=time.time()
    tlS1=[set()]
    S1=set()
    S1=S1.union(set(validLiterals))
    S1=S1.union(set(warLiterals))
    if(D):
        S1=S1.union(set(D))
    tlS1[0]=S1.difference(set([Q]))

    #Modificacio dec 11-> intentar detectar el conflicte abans de fer l'encoding!!<
    if Q.neg() in tlS1[0]:
        return True,[Q.neg()]


    #if(call==1):
    #    program.stats.conflic1Calls+=1
    #else:
    #    program.stats.conflict2Calls+=1

    #trS1 rules with head not in warranted
    trS1=[set()]
    i=0
    #sempre es contruiran els sets 0,1 i 2
    #iniciem amb tls1[0] construit
    while(i<=1):
        #construim el seguent trs1
        for clause in program.clauses[0]:
            if clause.head not in program.get_warranted(0,level):
                if clause.getBody() !=None and set(clause.body).issubset(tlS1[i]):
                    trS1[i].add((clause.head,tuple(clause.body)))
        #afegim a tls1 un el set previ
        tlS1.append(tlS1[i].copy())
        #afegim els possibles nous literals
        for rule in trS1[i]:
            if Clause(rule).head not in tlS1[i]:
                tlS1[i+1].add(Clause(rule).head)
        trS1.append(set())
        i=i+1
    i=i-1
    
    #print "trS1",trS1,i
    #now while literals set is diferent from previous iteration
    while(tlS1[i] != tlS1[i+1] or trS1[i] != trS1[i-1]):
        i+=1
        for clause in program.clauses[0]:
                if (clause.getBody() != None) and (set(clause.body).issubset(tlS1[i])):
                    trS1[i].add((clause.head,tuple(clause.body)))
        trS1.append(set())
        tlS1.append(tlS1[i].copy())
        for rule in trS1[i]:
            if(Clause(rule).head not in tlS1[i]):
                tlS1[i+1].add(Clause(rule).head) 
    t1=i
    #print "tlS1",tlS1,i
    #comensem el set 2
    S2=set()
    S2=S2.union(set(validLiterals))
    S2=S2.union(set(warLiterals))
    if(D):
        S2=S2.union(D)

    tlS2=[set(S2)]
    trS2=[set()]
    i=0
    while(i<=1):
        #print "***********",i
        for clause in program.clauses[0]:
            if (clause.getBody() != None) and (clause.getHead() not in program.get_warranted(0,level)):
                if set(clause.body).issubset(tlS2[i]):
                    trS2[i].add((clause.head,tuple(clause.body)))
        trS2.append(set())
        tlS2.append(tlS2[i].copy())
        i+=1
        for rule in trS2[i-1]:
            if Clause(rule).head not in tlS2[i-1]:
                tlS2[i].add(Clause(rule).head)

    i=i-1
    #print "trS2",trS2,i

    while(tlS2[i] != tlS2[i+1] or trS2[i] != trS2[i-1]):
#    while(i<len(tlS2[i])):
        i=i+1
        for clause in program.clauses[0]:
            if (clause.body and clause.head not in program.get_warranted(0,level)):
                if set(clause.body).issubset(tlS2[i]):
                    trS2[i].add((clause.head,tuple(clause.body)))
        trS2.append(set())
        tlS2.append(tlS2[i].copy())
        for rule in trS2[i]:
            if Clause(rule).head not in tlS2[i]:
                tlS2[i+1].add(Clause(rule).head)
    t2=i
    #print "tlS2",tlS2,i

    ##print "|->",Q,"<-| in ", tlS2[0],"? ", Q in tlS2[0]
    #utilitzarem llistes de diccionaris
    #per cada nivell en tl crearem un  diccionari en literals
    #per cada nivell en tr crearem un  diccionari en literals
    lnum=0
    literals1=[]
    for level in range(0,t1+1):
        literals1.append(myDict())
        for literal in tlS1[level]:
            literals1[lnum].pushitem(literal)
        lnum+=1
    ##print "Literals 1:",literals1

    lnum=0
    literals2=[]
    for level in range(0,t2+1):
        literals2.append(myDict())
        for literal in tlS2[level]:
            literals2[lnum].pushitem(literal)
        lnum+=1
    ##print "Literals 2:",literals2

    rules1=[]
    lnum=0
    #Afegeixo les regles a una MyList
    for level in range(0,t1+1):
        rules1.append(myDict())
        for rule in trS1[level]:
            #lo de la tuple es una chapusa per fer una regla hashable
            rules1[lnum].pushitem(rule)
        lnum+=1

    rules2=[]
    lnum=0
    #Afegeixo les regles a una MyList
    for level in range(0,t2+1):
        rules2.append(myDict())
        for rule in trS2[level]:
            #lo de la tuple es una chapusa per fer una regla hashable
            rules2[lnum].pushitem(rule)
        lnum+=1

    #generarem les variables per als conflices
    conflicts=myDict()
    
    for literal in tlS2[t2]:
        if Literal(literal).neg() in tlS2[t2] and (literal.neg(),literal) not in conflicts:
            conflicts.pushitem((literal,literal.neg()))
#    #print "Conflicts:",conflicts
    ##print "######################"
    #If no opposite literas can be derived, no conflict will be found
    if(len(conflicts)==0): return False,[]

    

    cnf=ConjunctiveNormalFormula("%s-%i" % (program.fileName,numEnc))
    cnf.comment("Query q:"+Q+", vc:"+str(validLiterals)+", wl:"+str(warLiterals)+", D:"+str(D)+"\n")
    cnf.comment("Warranted:"+str(program.get_warranted(0,level)))
    cnf.comment("Literals tlS1 at level t1:")
    cnf.comment("---Level "+str(t1)+"---")
    cnf.comment(str(literals1[t1]))
    cnf.comment("Literals trS1:")
    for idx,l in enumerate(literals2):
        cnf.comment("---Level "+str(idx)+"---")
        cnf.comment(str(l))
    cnf.comment("Literals trS2:")
    for idx,l in enumerate(rules2):
        cnf.comment("---Level "+str(idx)+"---")
        cnf.comment(str(l))
    numEnc=numEnc+1
    

    #-The true literals from VL2 that are in W U VC\{Q} mus also be true at VL1
    cnf.comment("The true literals from VL2 that are in W U VC\{Q} mus also be true at VL1")
    for literal in tlS2[0]:
        if literal in tlS1[t1] and literal != Q:
            cnf.comment("Literal from 1 level "+str(t1)+"("+literal+" literal from 2 level "+str(0)+" "+literal)
            cnf.push(literals1[t1][literal]+" -"+literals2[0][literal])

    #-The true literals from VL1 do not generate conflict with the strict knowledge
    cnf.comment("True literals from VL1 do not generate conflict with the strict knowledge")
    ##1-.No contradictory literals L and ~L, with L,~L\in TlS1(t1), can be true. We add the following clause:
    cnf.comment("1-.No contradictory literals L and ~L, with L,~L\in TlS1(t1), can be true. We add the following clause:")
    ##print("1-.No contradictory literals L and ~L, with L,~L\in TlS1(t1), can be true. We add the following clause:")
    cnf.comment("    Is "+literal+" in "+str(tlS1[t1]))
    conflict=[]
    for literal in tlS1[t1]:
        if Literal(literal).neg() in tlS1[t1] and  Literal(literal).abs() not in conflict:
            cnf.comment("conflict at level "+str(t1)+" > "+str(literal)+" "+str(Literal(literal).neg()))
            cnf.push("-"+literals1[t1][literal]+" -"+literals1[t1][Literal(literal).neg()])
            conflict.append(Literal(literal).abs())
    ##2-.A strict rule must be used when its body is true for literlas from VL1

    cnf.comment("2-.A strict rule must be used when its body is true")
    cnf.comment(str(trS1))
    for rule in program.clauses[0]:
        cnf.comment(str(rule))
        good=False
        if rule.getHead() in literals1[t1].keys():
            good=True
            clause=literals1[t1][Literal(rule.getHead())]
            if(rule.getBody() != None):
                for literal in rule.getBody():
                    if literal in literals1[t1].keys():
                        clause=clause+" -"+literals1[t1][Literal(literal)]
                    else:
                        good=False
            else:
                good=False
            if(good):
                cnf.push(clause)

    #The true literals from VL2 generate a conflict with the strict knowledge
    cnf.comment("The true literals from VL2 generate a conflict with the strict knowledge")
    ##1-.Because we force that the ser S encoded in VL1 does not generate a conflict, the conflict we are looking for, must necessary use Q
    cnf.comment("1-.Because we force that the ser S encoded in VL1 does not generate a conflict, the conflict we are looking for, must necessary use Q")
    ##print literals2[0][Q]
    ##print "|->",Q,"<-|"
    cnf.push(literals2[0][Q])

    ##2-.We need at least a conflict generated with the strict knowledge and the selected subset of literals
    cnf.comment("2-.We need at least a conflict generated with the strict knowledge and the selected subset of literals")
    clause=""
    for conflict in conflicts:
        clause=clause+conflicts[conflict]+" "
    ##print clause
    cnf.push(clause)
    
    ##3-.A conflict needs its two corresponding contradictory literals to be true at the end
    cnf.comment("3-.A conflict needs its two corresponding contradictory literals to be true at the end")
    for conflict in conflicts:
        ##print "-"+conflicts[conflict]+" "+literals2[t2-1][conflict[0]]
        cnf.comment(str(conflict)+" generated by... "+str(conflict[0])+" and "+conflict[1])
        cnf.push("-"+conflicts[conflict]+" "+literals2[t2][conflict[0]])
        ##print "-"+conflicts[conflict]+" "+literals2[t2-1][conflict[1]]
        cnf.push("-"+conflicts[conflict]+" "+literals2[t2][conflict[1]])

    ##4-.If a literal is true at step i it is also true at step i+1
    cnf.comment("4-.If a literal is true at step i it is also true at step i+1")
    for i in range(0,t2):
        for literal in tlS2[i]:
            ##print literal+"->","-"+literals2[i][literal], literals2[i+1][literal]
            cnf.comment(literal+"->  -"+literal+" at "+str(i)+" "+literal+" at "+str(i+1))
            cnf.push("-"+literals2[i][literal]+" "+literals2[i+1][literal])
    ##5-.Any literal from W must be set to true
    cnf.comment("5-.Any literal from W must be set to true")
    for literal in program.get_warranted(0,level):
        ##print literals2[0][literal]
        cnf.comment("Literal "+literal+" set to true")
        cnf.push(literals2[0][literal])
    ##6-.A literal true at step i needs a producing rule at step i-1 or to be true at step i-1
    cnf.comment("6-.A literal true at step i needs a producing rule at step i-1 or to be true at step i-1")
    for i in range(1,t2+1):
        for literal in tlS2[i]:
            predLit=False
            predRul=False
            clause="-"+literals2[i][literal]
            debug=literal+" at level "+str(i)
            if literal in tlS2[i-1]:
                predLit=True
                clause=clause+" "+literals2[i-1][literal]
                debug=debug+" "+literal+" at level "+str(i-1)
            #haurien de tornar totes les rules (pot ser que n'hi hagi mes d'una)
            producingRules=program.getBodyByHead(0,literal)
            if(producingRules):
                for producingRule in producingRules:
                    if (literal, tuple(producingRule)) in rules2[i-1].keys():
                        debug=debug+literal+" | rule: "+str(producingRule)
                    ##print producingRule
                        clause=clause+" "+rules2[i-1][(literal, tuple(producingRule))]
                        predRul=True
            ##print clause
            cnf.comment(debug)
            if(predLit or predRul):
                cnf.push(clause)

    ##7-.A rule used at step i needs its set of body literals to be true at step i
    cnf.comment("7-.A rule used at step i needs its set of body literals to be true at step i")
    for i in range(0,t2):
        for rule in trS2[i]:
            for literal in rule[1]:
                cnf.comment("Rule "+str(rule)+" literal: "+literal)
                cnf.push("-"+rules2[i][rule]+" "+literals2[i][literal])
    ##8-.A rule is used at most once
    cnf.comment("8-.A rule is used at most one")
    for leveli in range(0,t2+1):
        for levelj in range(leveli+1,t2):
            for rule in rules2[leveli]:
                ##print rules2[leveli][rule], rules2[levelj][rule],leveli,levelj
                cnf.push("-"+rules2[leveli][rule]+" -"+rules2[levelj][rule])
                
    
#    #print "|===> SAT Conflict DEBUG: for "+Q+" fil:    "+cnf.fil

    enctim2=time.time()-enctim1
    __builtin__.CONFLENCTIME=CONFLENCTIME+enctim2

    solution=cnf.solve("minisat")
    ##print solution[0]

    DEBUG=False
    if solution[0]!="UNSAT":
        if DEBUG:
            ##print "Entra a debug"
            
            outSol=[]
            debFil="%s-%i-conflict.debug" % (program.fileName,numEnc-1)
            #print "          |=********==> SAT DEBUG in file %s <===|" % (debFil)
            #print "          |=********==> SAT ENCODING in file %s <===|" % cnf.fil
            
            f=open(debFil,"w")
            f.write("=================QUERY================\n")
            f.write(" Checking if exists a conflict with "+Q+" \n")
            f.write("=================PROGRAM================\n")
            f.write(str(program))
            f.write("=================SOLUTION================\n")
            s={}
            for idx,el in enumerate(solution[1]):
                if(int(el)>0):
                    f.write("("+str(idx+1)+","+el+"), ")
                else:
                    f.write("(-"+str(idx+1)+","+el+"), ")
                s[abs(int(el))]=idx+1
                if((int(idx)%10)==0):
                    f.write("\n")  
            f.write("\n\ns:"+str(s)+"\n\n")
            f.write("\n=================WOLOLOLOLOOOOOO================\n")
            f.write("Literals tlS1:")
            for idx,l in enumerate(literals1):
                f.write("---Level "+str(idx)+"---\n")
                for el in l:
                    if int(l[el]) in s.keys():
                        f.write("            "+el+" : "+str(s[int(l[el])])+"\n")
            f.write("Rules trS1:\n")
            for idx,l in enumerate(rules1):
                f.write("---Level "+str(idx)+"---\n")
                for el in l:
                    if int(l[el]) in s.keys():
                        f.write("            "+str(el)+" : "+str(s[int(l[el])])+"\n")
            f.write("Literals tlS2:")
            #print "Literals tlS2:"
            for idx,l in enumerate(literals2):
                f.write("---Level "+str(idx)+"---\n")
                #print "---Level "+str(idx)+"---\n"
                for el in l:
                    if int(l[el]) in s.keys():
                        f.write("            "+el+" : "+str(s[int(l[el])])+"\n")
                        ##print "            "+el+" : "+str(s[int(l[el])])+"\n"
                        #print el, l[el], str(s[int(l[el])])
            f.write("Rules trS2:")
            for idx,l in enumerate(rules2):
                f.write("---Level "+str(idx)+"---\n")
                for el in l:
                    if int(l[el]) in s.keys():
                        f.write("            "+str(el)+" : "+str(s[int(l[el])])+"\n")     
           
            f.write("conflict generated ("+str(conflicts)+"):\n")
            for conflict in conflicts:
                if s[int(conflicts[conflict])] in conflicts.keys() and int(solution[1][s[int(conflicts[conflict])]])>0:
                    f.write("\nConflict activated: "+str(conflict)+"\n")

            f.write("\nActivated rules S1:\n")
            #print "Activated rules S1:\n"
            for leveli in range(0,t1):
                #print " -Level "+str(leveli)+":  \n"
                for rule in rules1[leveli]:
                    if rules1[leveli][rule] in s.keys():
                        if int(solution[1][s[int(rules1[leveli][rule])]-1])>0:
                            f.write("rule "+str(rule)+"\n")
                            #print "rule "+str(rule)+" :"+str(s[int(rules1[leveli][rule])])+" \n"

            f.write("Activated rules S2:\n")
            #print "Activated rules S2:\n"
            for leveli in range(0,t2):
                f.write(" -Level "+str(leveli)+":  \n")
                #print " -Level "+str(leveli)+":  \n"
                for rule in rules2[leveli]:
                    if int(solution[1][s[int(rules2[leveli][rule])]-1])>0:
                        #print "rule "+str(rule)+" :"+str(s[int(rules2[leveli][rule])])+" \n"
                        f.write("rule "+str(rule)+" :"+str(s[int(rules2[leveli][rule])])+" \n")

            f.write("\nActivated valid literals S1:\n")       
            f.write(" -Level "+str(t1)+":  \n")
            for leveli in range(0,t1+1):
                #print "=====",leveli,"======"
                for literal in literals1[t1]:
                    try:
                        if int(solution[1][s[int(literals1[t1][literal])]-1])>0:
                            f.write("literal "+str(literal)+" :"+str(s[int(literals1[t1][literal])])+" \n")
                            #print "literal from 1:   "+str(literal)+" :"+str(s[int(literals1[t1][literal])])+" \n"
                    except:
                        pass
            f.write("\nActivated valid literals S2:\n")
            act_lit=[]
            for leveli in range(0,t2+1):
                #print "=====",leveli,"======"
                f.write(" -Level "+str(leveli)+":  \n")
                for literal in literals2[leveli]:
                    if int(solution[1][s[int(literals2[leveli][literal])]-1])>0:
                        f.write("literal "+str(literal)+" :"+str(s[int(literals2[leveli][literal])])+" \n")
                        #print "literal from 2:    "+str(literal)+" :"+str(s[int(literals2[t1][literal])])+" \n"
                        act_lit.append(literal)

            f.write("\n=================ENCODING================\n")

            f.write("encoding file: %s\n" % cnf.fil)
           
            f2=open(cnf.fil,"r")
            f.write(f2.read())
            f2.close()
            os.system("cat %s >> %s " % (cnf.fil,debFil))
            f.close()

        #print ":::::::::::::::::::::::::::::::::::::::::::::::"
        s={}
        for idx,el in enumerate(solution[1]):
            s[abs(int(el))]=idx+1
        act_lit=[]
        for literal in literals2[t2]:
            if int(solution[1][s[int(literals2[leveli][literal])]-1])>0:
                ##print "literal from 2:    "+str(literal)+" :"+str(s[int(literals2[t1][literal])])+" \n"
                act_lit.append(literal)
        

        for conflict in conflicts.values():
        ##print "conflict:", conflict, solution
            try: solution[1].index(conflict)
            except:
                pass
            else:
                return True,act_lit
        return False,[]
    else:
        return False,[]


def conflictASP(program,level,Q,validLiterals,warLiterals,D,call):
    global numEnc
    numEnc=numEnc+1
    asp=PyASP.ProgramASP("%s-%iASP" % (program.fileName,numEnc))
    s1={}
    s3={}
    s2={}
    vars1=[]
    vars2=[]
    conflicts1=[]
    conflicts2={}
    
    ##print "\n==============QUERY============"
    ##print "Query: Q: "+Q+" ValidLiterals: "+str(validLiterals)+" WarrantedLiterals: "+str(warLiterals)+" D: "+str(D)+"\n"
    #generate sets
    #set of predicates
    #=============TODO======generar d'una manera mes sencilla========

   
    if D!=None:
        S=[e for e in validLiterals+D if e!=Q]
    else:
        S=[e for e in validLiterals if e!=Q]

    #Modificacio dec 11-> intentar detectar el conflicte abans de fer l'encoding!!<
    if Q.neg() in S:
        #print S, "*conlficte a la vista", Q
        return True,[Q.neg()]
    ##print "Set S:",S
    
    asp.addComment("Adding predicates (almost valid)")
    for lit in S:
            pred1=PyASP.Predicate("e",lit+"1",2)
            asp.addPredicate(pred1)
            s1[lit+"1"]=pred1
            asp.addComment(" - literal: "+str(pred1))
            pred3=PyASP.Predicate("e",lit+"3",2)
            asp.addPredicate(pred3)
            s3[lit+"3"]=pred3
            asp.addComment(" - literal: "+str(pred3))


    pred3=PyASP.Predicate("e",Q+"3",2)
    asp.addComment(" - literal: "+str(pred3))
    asp.addPredicate(pred3)
    s3[Q+"3"]=pred3

    #=================================================================
    #==========TODO========fer un metode per obtenir totes les variables
    #vars1.append(str(Q)+"1")
    for clauses in program.clauses:
        for rule in clauses:
            if(rule.getHead()):
                if(rule.getHead()+"1" not in s1.keys() and rule.getHead()+"1" not in vars1):
                    vars1.append(str(rule.getHead())+"1")
                if(rule.getHead()+"2" not in s2.keys() and rule.getHead()+"2" not in vars2):
                    vars2.append(str(rule.getHead())+"2")
            if(rule.getBody()):    
                for var in rule.getBody():
                    if var+"1" not in s1.keys() and var+"1" not in vars1:
                        vars1.append(str(var)+"1")
                    if var+"2" not in s2.keys() and var+"2" not in vars2:
                        vars2.append(str(var)+"2")
    for var in vars1+vars2:
         asp.addVar(PyASP.Variable(var))
    #=========================================================================

    ##print "Q:", Q
    ##print "Variables:", asp.variables
    ##print "Predicates:", asp.predicates
    ####################################################################################
    # Adding rules and conflict constraints for variables and predicates from group 1!!#
    ####################################################################################
    asp.addComment(" Adding rules and conflict constraints for variables and predicates from group 1!!")
    for rule in program.clauses[0]:
        ##print rule.getHead(), rule.getBody()
        asp.addComment("  - rule:"+str(rule))
        if(rule.getBody()!=None):
            r=PyASP.Rule(asp.atomize(rule.getHead()+"1"),asp.atomize(map(lambda x: x+"1",rule.getBody())))
            ##print "------>",r
            asp.addRule(r)

        elif(rule.getBody()==None):
            r=PyASP.Rule(asp.atomize(rule.getBody()),asp.atomize(rule.getHead()+"1"))
            ##print "------>",r
            asp.addRule(r)    

    ##print "RULES:",asp.rules
    ##print s1
    ##print vars1

    #3-.Check for possible conflicts
    #================TODO=============aixo es una mica un axapusa
    heads_strictpart=[r.getHead() for r in program.clauses[0]]
    heads_strictpart+=program.get_warranted(0,level)
    ##print "Heads stric part",heads_strictpart
    #============================================================
    asp.addComment("Check for possible conflicts")
    for var in s1.keys()+[e+"1" for e in heads_strictpart]:
        ##print "   - Checking for possible conflicts with "+var+" in set ..."+str(s1.keys())
        t=re.match("^([\~]*)([a-zA-Z]+[\d]*)$",var)
        if(t):
            ##print "check for literal",t.group(1)+t.group(2), " in ",  s1.keys()
            if (t.group(1)) and  (t.group(2) in s1.keys()+[e+"1" for e in heads_strictpart]) \
                    and (t.group(2) not in conflicts1):
                
                asp.addComment(str(s1.keys()))
                asp.addComment("@@@@@@@@@@@@@ conflict with "+t.group(2)+" and ~"+t.group(2))
                conflicts1.append(t.group(2))
                c=PyASP.Variable("c"+t.group(2))
                asp.addVar(c)
                asp.addRule(PyASP.Rule(c,[asp.atomize(t.group(2)),asp.atomize("~"+t.group(2))]))
                ##print "------>",PyASP.Rule(c,[asp.atomize(t.group(2)),asp.atomize("~"+t.group(2))])
                asp.addRule(PyASP.Rule(PERP,asp.getVar("c"+t.group(2))))
                ##print "---NONEEEE--->",PyASP.Rule(PERP,asp.getVar("c"+t.group(2)))
            elif (t.group(1)==None) and ("~"+t.group(2) in s1.keys()+[e+"1" for e in heads_strictpart]) \
                    and (t.group(2) not in conflicts1):
                asp.addComment("@@@@@@@@@@@@@ conflict with ~"+t.group(2)+" and "+t.group(2))
                conflicts1.append(t.group(2))
                c=PyASP.Variable("c"+t.group(2))
                asp.addVar(c)
                asp.addRule(PyASP.Rule(c,[asp.atomize(t.group(2)),asp.atomize("~"+t.group(2))]))
                ##print  "------>",PyASP.Rule(c,[asp.atomize(t.group(2)),asp.atomize("~"+t.group(2))])
                ##print "----->",PyASP.Rule(PERP,asp.getVar("c"+t.group(2)))
                asp.addRule(PyASP.Rule(PERP,asp.getVar("c"+t.group(2))))
               
    
    ####################################################################################
    # Adding rules and conflict constraints for variables and predicates from group 2!!#
    ####################################################################################
    #s'ha de diferenciar les head de les rules de les vc i D
    ##print s2
    ##print vars2
    asp.addComment("Adding rules and conflict constraints for variables and predicates from group 2!")
    for rule in program.clauses[0]:
        asp.addComment("  - rule:"+str(rule))
        if(rule.getBody()):
            r=PyASP.Rule(asp.atomize(rule.getHead()+"2"),asp.atomize(map(lambda x: x+"2",rule.getBody())))
            ##print "------>",r
            asp.addRule(r)
        elif(rule.getBody()==None):
            r=PyASP.Rule(asp.atomize(rule.getBody()),asp.atomize(rule.getHead()+"2"))
            ##print "------>",r
            asp.addRule(r)   

    #3-.Check for possible conflicts
    ##print "S22222222",s2.keys(),str([e+"2" for e in heads_
    for var in s3.keys():
        t=re.match("^([\~]*[a-zA-Z]+[\d]*)3$",Literal(var).abs())
        l=Literal(t.group(1)+"2")
        if l in vars2 and l.neg() in vars2 and l.abs() not in conflicts2.keys():
            ##print "Conflict "+l+" "+l.neg()
            c=PyASP.Variable("c"+l.abs())
            conflicts2[l.abs()]="c"+l.abs()
            asp.addVar(c)
            r=PyASP.Rule(c,[asp.atomize(l),asp.atomize(l.neg())])
            ##print "------>",r
            asp.addRule(r)
    for var in [e+"2" for e in heads_strictpart]:
        t=re.match("^([\~]*[a-zA-Z]+[\d]*)2$",Literal(var).abs())
        l=Literal(t.group(1)+"2")
        if l in vars2 and l.neg() in vars2 and l.abs() not in conflicts2.keys():
            ##print "Conflict "+l+" "+l.neg()
            c=PyASP.Variable("c"+l.abs())
            conflicts2[l.abs()]="c"+l.abs()
            asp.addVar(c)
            r=PyASP.Rule(c,[asp.atomize(l),asp.atomize(l.neg())])
            ##print "------>",r
            asp.addRule(r)

    #if len(conflicts2)==0:
    #    return False
    cs=PyASP.Variable("cs")
    asp.addVar(cs)

        
    ##print PyASP.Rule(cs,asp.atomize(conflicts2.values()))
    ##print "-------->",PyASP.Rule(cs,asp.atomize(conflicts2.values()))
    #asp.addRule(PyASP.Rule(cs,asp.atomize(conflicts2.values())))
    if len(conflicts2)==0: return False,[]
    asp.addRule(PyASP.CardinalityRule(cs,asp.atomize(conflicts2.values()),1))
    ##print "-------->",PyASP.Rule(PERP,cs.neg())
    asp.addRule(PyASP.Rule(PERP,cs.neg()))
    asp.addComment("Q ("+Q+" must be true")
    asp.addRule(PyASP.Rule(None,asp.atomize(Q+"2")))
    #####################################
    #   Linking rules                   #
    #####################################

    for pred in s1:
        t=re.match("^([\~]*)([a-zA-Z]+[\d]*)1$",pred)
        asp.addComment(pred+" "+t.group(1)+t.group(2)+"3")
        asp.addRule(PyASP.Rule(asp.atomize(pred).encode(1),asp.atomize(t.group(1)+t.group(2)+"3").encode(1)))

    ############
    #   enforce vc u D to make variables from S2 true
    #############

    for pred in s3:
        t=re.match("^([\~]*)([a-zA-Z]+[\d]*)3$",pred)
        ##print asp.atomize(t.group(1)+t.group(2)+"2").encode(),asp.atomize(pred).encode(1)
        asp.addComment(t.group(1)+t.group(2)+"2 "+pred)
        asp.addRule(PyASP.Rule(asp.atomize(t.group(1)+t.group(2)+"2").encode(),asp.atomize(pred).encode(1)))

    #adding warranted
    for lit in warLiterals:
        r=PyASP.Rule(None,asp.atomize(lit+"1"))
        asp.addRule(r)
        r=PyASP.Rule(None,asp.atomize(lit+"2"))
        asp.addRule(r)
    sol=asp.solve()
    #print sol

    DEBUG=False
    if(DEBUG):
        debFil="%s.confl-debug" % asp.fil
        #print "               |===========> Query: Q: "+Q+" ValidLiterals: "+str(validLiterals)+" WarrantedLiterals: "+str(warLiterals)+" D: "+str(D)
        #print "               |===========> DEBUG in file %s <===========|" % debFil
        f=open(debFil,"a")
        f.write("   %s   \n" % asp.fil)
        os.system("cat %s > %s" % (asp.fil,debFil))

        f.write("==============QUERY============\n")
        f.write("Query: Q: "+Q+" ValidLiterals: "+str(validLiterals)+" WarrantedLiterals: "+str(warLiterals)+" D: "+str(D)+"\n")
        f.write("==============SOLUTION============\n")
        f.write(str(sol[2])+"\n")
        if sol[0]==True:
            fsol={}
            for i in range(0,len(sol[1])):
                t=re.match("^v\((\d+)\)$",sol[1][i])
                r=re.match("^e\((\d+),(\d)\)$",sol[1][i])
                if t:
                    fsol[sol[2][i]]=(t.group(1),True)
                if r:
                    if r.group(2) == "1":
                        fsol[sol[2][i]]=(r.group(1),True)
                    else:
                        fsol[sol[2][i]]=(r.group(1),False)
            f.write("Conflicts:\n")
            for lit in fsol:
                tt=re.match("^c(.*)",lit)
                if fsol[lit][1] == True and tt:
                    f.write(lit+" "+": True\n")
                
            f.write("Activated literals in 1:\n")
            for lit in fsol:
                tt=re.match("(.*)1$",lit)
                if fsol[lit][1] == True and tt:
                    f.write(lit+" "+": True\n")

            r1=[]
            r2=[]
            f.write("Activated rules in 1:\n")
            for rule in program.clauses[0]:
                llll=""
                if len(rule)>1:
                    active=True
                    for literal in rule[1]:
                        if literal+"1" in fsol.keys() and fsol[literal+"1"][1]==True and active:
                            llll=llll+str(literal)+" "
                            active=True
                        elif literal+"1" in fsol.keys() and fsol[literal+"1"][1]==False:
                            active=False
                        else:
                            active=False
                    if active:
                        r1.append(rule)
                        
                        f.write(llll+"\n"+str(rule)+" "+": True\n")

            f.write("Activated literals in 2:\n")
            for lit in fsol:
                tt=re.match("(.*)2$",lit)
                if fsol[lit][1] == True and tt:
                    f.write(lit+" "+": True\n")

#            f.write("\nfsol:"+str(fsol)+"\n")

            f.write("Activated rules in 2:\n")
            for rule in program.clauses[0]:
                if len(rule)>1:
                    active=True
                    literals=[]
                    for literal in rule[1]:
                        if literal+"2" in fsol.keys() and fsol[literal+"2"][1]==True and active:
                            literals.append(fsol[literal+"2"])
                            active=True
                        elif literal+"2" in fsol.keys() and fsol[literal+"2"][1]==False:
                            active=False
                        else:
                            active=False
                    if active and len(literals)>0:
                        r2.append(rule)
                        f.write(str(rule)+" "+": True--->"+str(literals)+"\n")

            f.write("Rules not in R1\n")        
            for r in r2:
                if r not in r1:
                    f.write(str(r)+"\n")
#        f.write("==============VARIABLES============\n")
#        for el in asp.variables:
#            f.write(str(el)+"->"+str(asp.variables[el])+"\n")
    act_literals=[]
    if sol[0]==True:
        fsol={}
        for i in range(0,len(sol[1])):
            t=re.match("^v\((\d+)\)$",sol[1][i])
            r=re.match("^e\((\d+),(\d)\)$",sol[1][i])
            if t:
                fsol[sol[2][i]]=(t.group(1),True)
            if r:
                if r.group(2) == "1":
                    fsol[sol[2][i]]=(r.group(1),True)
                else:
                    fsol[sol[2][i]]=(r.group(1),False)
        #print conflicts2.keys()
        #print "Activated literals in 2:"
        for lit in fsol:
            tt=re.match("(.*)2$",lit)
            tt2=re.match("^c(.*)",lit)
            if fsol[lit][1] == True and tt and not tt2:
                #print tt.group(1)+" "+": True"
                act_literals.append(tt.group(1))
    #print "*********?????????******"
    if sol[0]==False:
#        c=raw_input("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        print act_literals
    return sol[0],act_literals



            


def almost_validSAT(program,q,p,vc,level,method):
    global numEnc
    enctim1=time.time()
    #literals a nivell 0 son:
    #     - valid literals
    #     - warranted

    #first we check in almost valid cache
    #if there's no argument for that pair whe serach for an argument
    #else if none: it means that in a previous search no argument was found
    #then, no argument will be found anymiore
    #else: an argument is still almost valid
#    try: argument=program.almostValidCache[(p,q)]
#    except KeyError:
#        program.stats.almostValidCalls+=1
        ##print program.stats.almostValidCalls
#        pass

    av_cache_status=program.almostValidCache.check(p,q)
    if av_cache_status != None:
        ##print "----> AlmostValidCache response for %s %s" % (p,q)
        return av_cache_status
        
    if p in program.get_warranted(0,level) or p in program.get_blocked(0,level) or Literal(p).neg() in program.get_blocked(0,level):
        ##print "p is warranted, blocked or its dual blocked"
        return False

#    #print "Checking if ",p," is AV wrt ", q
    #creem els sets de literals i regles
    tl=[set(program.get_warranted(0,level))]
    tr=[[]]
    #creem el set per restar-lo del set de literals
    notInTl=set([q,Literal(p).neg()])
    #ho treiem del set de literals
    tl[0].update(set(vc).difference(notInTl))

    #creem el set de alpha rules i strict rules
    strict_rules=[rule for rule in program.getStrictRules() if rule[0] not in program.get_blocked(0,level)]
    alpha_rules=program.getAlphaRules(level)
    #print ">>>>>",alpha_rules
    i=0
    while(i<=1):
        #si es arule podem escollir si l'elegim o no si el head es q
        for arule in alpha_rules:
            if arule[0] != q and set(arule[1]).issubset(set(tl[i])):
                tr[i].append(arule)
        #pero si es srule han de ser totes!
        for srule in strict_rules:
            if set(srule[1]).issubset(set(tl[i])):
                tr[i].append(srule)
        tl.append(set())
        tl[i+1]=tl[i].copy()
        for rule in tr[i]:
            if rule[0] not in tl[i]:
                tl[i+1].add(rule[0])
        tr.append([])
        i=i+1

    i=i-1

    while ((tl[i] != tl[i+1]) or (tr[i] != tr[i-1])):
    #while(i<len(tr[i])):
        i=i+1
        for arule in alpha_rules+strict_rules:
            if arule[0] != q and set(arule[1]).issubset(set(tl[i])):
                tr[i].append(arule)
        for srule in strict_rules:
            if set(srule[1]).issubset(set(tl[i])):
                tr[i].append(srule)
        tl.append(set())
        tl[i+1]=tl[i].copy()
        for rule in tr[i]:
            if rule[0] not in tl[i]:
                tl[i+1].add(rule[0])
        tr.append([])

    t=i+1

    ##print "El closure es:",tl[t]
    lnum=0
    literals=[]
    #utilitzarem llistes de diccionaris
    #per cada nivell en tl crearem un  diccionari en literals
    #per cada nivell en tr crearem un  diccionari en literals

    for level in range(0,t+1):
        literals.append(myDict())
        for literal in tl[level]:
            literals[lnum].pushitem(literal)
        lnum+=1

    lnum=0
    rules=[]
    #Afegeixo les regles a una MyList
    for level in range(0,t):
        rules.append(myDict())
        for rule in tr[level]:
            #lo de la tuple es una chapusa per fer una regla hashable
            rules[lnum].pushitem((rule.head,tuple(rule.body)))
        lnum+=1

    #comprovem que p estigui al nivell t
    if p not in tl[t]:
        ##print tl[0], "not in tl[t]"
        ##print "P is not in tl[t]"
        return False

    #This is madness! NO! This is SAT-ENCODING!
    ##print "Literals:",literals
    ##print "Rules:",rules
    cnf=ConjunctiveNormalFormula("%s-SAT%i" % (program.fileName,numEnc))
    numEnc=numEnc+1
    ##print "                          :::> SAT-DEBUG:","%s-%i" % (program.fileName,numEnc)
    #1-the literal P must be true and the end at the end of the argument
    for l in tl:
        cnf.comment("-----------------level-------------")
        cnf.comment(str(l))
    for l in tr:
        cnf.comment("-----------------level-------------")
        cnf.comment(str(l))
    cnf.comment("1-the literal P must be true and the end at the end of the argument")
    cnf.comment(p)
    if p in literals[t]:
        cnf.push(literals[t][p])

    #2-the set of true literals is consistent
    cnf.comment("2-the set of true literals is consistent")
    confls=[]
    conflicts=[]
    for i in range(0, len(literals)):
        conflicts.append([])

    for leveli in range(0, t+1):
        for levelj in range(leveli, t+1):
            for literal in literals[leveli]:
                if (Literal(literal).neg() in literals[levelj]) and  (Literal(literal).abs()+"-"+str(leveli)+"-"+str(levelj) not in confls) :
                    ##print literal+" "+literal.neg()
                    ##print "-"+literals[leveli][literal]+" -"+literals[levelj][Literal(literal).neg()], "("+literal+" "+literal.neg()+")"
                    cnf.comment(literal+" "+str(leveli)+" "+literal.neg()+" "+str(levelj))
                    cnf.push("-"+literals[leveli][literal]+" -"+literals[levelj][Literal(literal).neg()])
                    confls.append(Literal(literal).abs()+"-"+str(leveli)+"-"+str(levelj))

    #3-if a literal is true at step i it is also true at step i+1
    cnf.comment("3-if a literal is true at step i it is also true at step i+1")
    for leveli in range(0, t):
        for literal in literals[leveli]:
            cnf.comment(literal+" at steps"+str(leveli)+" "+str(leveli+1))
            cnf.push("-"+literals[leveli][literal]+" "+literals[leveli+1][literal])

    #4-any literal from W must be set to true
    cnf.comment("4-any literal from W must be set to true")
    for literal in program.get_warranted(0,level):
        cnf.comment(literal)
        cnf.push(literals[0][literal])
 
    #5-S'ha passat a la nova part de la formula

    #6-a literal true at step i needs a producing rule at step i-1 or to be true at step i-1
    #NOTE that a literal at step 1 can be produced by a rule or literal at step i-1 or both!
    #that means it can be a (fact or a literal) or (a rule) or both but at least one of them.
    cnf.comment("6-a literal true at step i needs a producing rule at step i-1 or to be true at step i-1")

    for leveli in range(1,t+1):
        for literal in literals[leveli]:
            exists=False
            clause=""
            cnf.comment(">> Literal "+literal+" at step "+str(leveli)+"<<")
            clause="-"+literals[leveli][literal]+" "
            #we check that literal exist in previous level
            if literal in literals[leveli-1]:
                exists=True
                cnf.comment("Found> Literal at previous step("+str(leveli-1)+"): ["+literal+"("+literals[leveli-1][literal]+")]")
                clause=clause+" "+literals[leveli-1][literal]
            #podria tornar una tupla, no?
            #literalBody=program.getBodyByHead(leveli-1,literal)
            #geni! gracies!
            literalBody=[rule[1] for rule in rules[leveli-1] if rule[0]==literal]
            if(literalBody!=None):
                cnf.comment("Found> ("+str(len(literalBody))+") Rule at previous level("+str(leveli-1)+"): rule-> "+literal+" "+str(literalBody))
                for body in literalBody:
                    cnf.comment("Body---> "+str(body))
                    if tuple([literal,tuple(body)]) in rules[leveli-1]:
                        exists=True
                        clause=clause+" "+rules[leveli-1][tuple([literal,tuple(body)])]
                        ##print "wtf?"+rules[leveli-1][tuple([literal,tuple(body)])]+str(body)
            if(exists):
                cnf.push(clause)

    #7-A rule used at step i needs its set of body literals to be true at step i
    cnf.comment("7-A rule used at step i needs its set of body literals to be true at step i")
    for leveli in range(0,t):
        cnf.comment("=============="+str(leveli)+"==================")
        for rule in rules[leveli]:
            #clause=""
            #clause=clause+"-"+str(rules[leveli][rule])+" "
            cnf.comment("Rule "+str(rule)+" needs:")
            for literal in rule[1]:
                #clause=clause+str(literals[leveli][literal])+" "
                cnf.comment("Literal: "+str(literal))
                cnf.push("-"+str(rules[leveli][rule])+" "+str(literals[leveli][literal]))
            #cnf.push(clause)
            
    #8-a rules is used at most once
    cnf.comment("8-a rules is used at most once")
    for leveli in range(0,t):
        for levelj in range(leveli+1,t):
            for rule in rules[leveli]:
                cnf.push("-"+rules[leveli][rule]+" -"+rules[levelj][rule])

    #9-no two defeasible rules produce the same literal
    cnf.comment("9-no two defeasible rules produce the same literal")
    arulesHeads=set()
    #we first obtain a list with alpha rules' heads
    for arule in alpha_rules:
        arulesHeads.add(arule.head)
    for lit in arulesHeads:
        #the check its bodies
        arulesBodies=program.getBodyByHead(level,lit)
        #If a head only have a producing body we skip.
        ##print rules
        
        if(arulesBodies and len(arulesBodies)>1):
            #else we combine in pairs
            for i in range(0,len(arulesBodies)):
                for j in range(i+1,len(arulesBodies)):
                    ##print (lit,tuple(arulesBodies[i])),(lit,tuple(arulesBodies[j]))
                    #and go across levels to obtain rules variables
                    for leveli in range(0,t):
                        for levelj in range(leveli,t+1):
                            ##print rules[leveli][(lit,tuple(arulesBodies[i]))]+" -"+rules[levelj][(lit,tuple(arulesBodies[j]))], (leveli,levelj)
                            if(rules[leveli].findKey((lit,tuple(arulesBodies[i]))) and rules[levelj].findKey((lit,tuple(arulesBodies[j])))):
                                   cnf.push(" -"+rules[leveli][(lit,tuple(arulesBodies[i]))]+" -"+rules[levelj][(lit,tuple(arulesBodies[j]))])
 

    #here we implement a new part devoted to check that literals involved in
    #the almost valid argument are consistent with strict part and warranted
    sl=myDict()
    strict_rules=program.getStrictRules()
    for lit in tl[t]:
        sl.pushitem(lit)
    for s in strict_rules:
        sl.pushitem(s[0])
        for literal in s[1]:
            sl.pushitem(literal)
    
    
    cnf.comment("1-. Literasl from tl[t] are true in strict knowledge")
    for literal in tl[t]:
        if literal in sl.keys():
            cnf.comment(literal)
            cnf.push("-"+literals[t][literal]+" "+sl[literal])
    
    cnf.comment("2a-. Warranted literals are set to true")
    for literal in program.get_warranted(0,level):
        if literal in sl.keys():
            cnf.comment(literal)
            cnf.push(sl[literal])

    cnf.comment("2b-. Blocked literals are set to false")
    for literal in program.get_blocked(0,level):
        if literal in sl.keys():
            cnf.comment(literal)
            cnf.push("-"+sl[literal])

    cnf.comment("3-. Rules with its body true, must be have its head true")
    for rule in strict_rules:
        shead=sl[rule[0]]
        clause=""
        for literal in rule[1]:
            clause=clause+"-"+sl[literal]+" "
        cnf.comment(str(rule))
        cnf.push(clause+shead)

    cnf.comment("4-. No conflicts can arise")
    conflicts=[]
    for literal in sl.keys():
        if Literal(literal).neg() in sl.keys() and Literal(literal).abs() not in conflicts:
            cnf.comment(literal+" "+Literal(literal).neg())
            cnf.push("-"+sl[literal]+" -"+sl[Literal(literal).neg()])
            conflicts.append(Literal(literal).abs())

    enctim2=time.time()-enctim1
    __builtin__.ALMVALENCTIME=ALMVALENCTIME+enctim2

    solution=cnf.solve(method)
   
    if solution[0]=="UNSAT":
        return False

    outSol=[]
    try: 
        sat=solution[0]
        solution=solution[1]
    except:
        program.almostValidCache.insert(p,q,[],False)
        return False

    for lit in literals[0]:
        argument=[]
        if (lit not in program.get_warranted()) and (literals[t][lit] in solution):
            argument.append(lit)
    literals_in_rule=[]        
    for lev in rules:
        for rul in lev:
            if lev[rul] in solution:
                literals_in_rule.append(rul[1][0])
    program.almostValidCache.insert(p,q,literals_in_rule,True)

    DEBUG=False
    if DEBUG:
        #show almost valid argument
        outSol=[]
        debFil="%s-%i.debug" % (program.fileName,numEnc-1)
        #print "          |===> SAT DEBUG in file %s <===|" % debFil
        #print "          |===> SAT ENCODING in file %s <===|" % cnf.fil
        f=open(debFil,"w")
        f.write("=================QUERY================\n")
        f.write(" Checking if "+p+" is almost valid with respect of "+q+"\n")
        f.write("Warranted: "+str(program.get_warranted(0,level)))
        f.write("Blocked: "+str(program.get_blocked(0,level)))
        f.write("=================PROGRAM================\n")
        f.write(str(program))
        f.write("=================SOLUTION================\n")
        for idx,el in enumerate(solution):
            if(int(el)>0):
                f.write("("+str(idx+1)+","+el+"), ")
            else:
                f.write("(-"+str(idx+1)+","+el+"), ")
            if((int(idx)%10)==0):
                f.write("\n")
                                
        f.write("\n=================WOLOLOLOLOOOOOO================\n")
        asol=[]
        v=0
        for l in literals:
            for el in l:
                if l[el] in solution:
                    asol.append((el,v,l[el]))
            v=v+1
                    
        f.write("sol:")
        for el in asol:
            f.write("\n>>>"+str(el))
        rsol=[]
        f.write("\nActivated rules:\n")
        for l in rules:
            for el in l:
                if l[el] in solution:
                    rsol.append((el,v,l[el]))

        f.write("sol:n")
        for el in rsol:
            f.write("\n>>>"+str(rsol))
        f.write("\n=================LITERALS================\n")
        for l in literals:
            f.write(str(l)+"\n")
        outSol=[]
        for variable in solution:
            variable=str(abs(int(variable)))
            for leveli in range(0,t+1):
                lit=literals[leveli].findKey(variable)
                if lit != [] and lit[0] not in outSol:
                    outSol.append((lit,leveli))
        f.write(str(outSol))
        f.write("\n=================ALPHA RULES================\n")
        for ar in alpha_rules:
            f.write(str(ar)+"\n")
        f.write("\n=================tr i tl================\n")
        for idx,l in enumerate(tr):
            f.write("------ Level "+str(idx)+"---\n")
            for el in l:
                f.write("   rule:"+str(el)+"\n")
        for idx,l in enumerate(tl):
            f.write("\n------ Level "+str(idx)+"---\n")                       
            for el in l:
                f.write("  "+str(el)+" ")
        f.write("\n=================ENCODING================\n")
        f.write("encoding file: %s\n" % cnf.fil)
        os.system("cat %s >> %s " % (cnf.fil,debFil))
        f.close()
       
 
    return True
                



def almost_validASP(program,q,p,vc,level):

    global numEnc
    numEnc=numEnc+1
    ##print "                   Checking if "+p+" is almost valid with respect of "+q+" valid literals: "+str(vc)
    ##print "     =|>Encoding almost valid "+str(numEnc)
    ##print "                          =|>"+q+" "+p
    #literals a nivell 0 son:
    #     - valid literals
    #     - warranted

    #first we check in almost valid cache
    #if there's no argument for that pair whe serach for an argument
    #else if none: it means that in a previous search no argument was found
    #then, no argument will be found anymiore
    #else: an argument is still almost valid
    av_cache_status=program.almostValidCache.check(p,q)
    if av_cache_status != None:
        #print "----> AlmostValidCache response for %s %s" % (p,q)
        return av_cache_status

    if p in program.get_warranted(0,level) or p in program.get_blocked(0,level) or Literal(p).neg() in program.get_blocked(0,level):
        ##print "p is warranted, blocked or its dual blocked"
        return False


    variables=[]
    predicates={}
    conflicts=[]

    asp=PyASP.ProgramASP("%s-%i" % (program.fileName,numEnc))

    #print asp.fil
    S=[Literal(e) for e in vc if e != q]
    asp.addComment("Warranted: "+str(program.get_warranted(0,level)))
    asp.addComment("Declarant predicats")
    for lit in S:
        asp.addComment("         %s" % lit)
        pred=PyASP.Predicate("e",lit,2)
        asp.addPredicate(pred)
        predicates[lit]=pred

    #get al the variables
    #TODO: check PDLP progam class to get variables in an easier way

    alpha_rules=program.getAlphaRules(level)
    for rule in alpha_rules:
        if rule.getHead() == q:
            alpha_rules.remove(rule)

    for rule in alpha_rules:
        if(rule.getHead()):
            if(rule.getHead() not in S) and (rule.getHead() not in variables):
                variables.append(Literal(rule.getHead()))
        if(rule.getBody()):    
            for var in rule.getBody():
                if (var not in S) and (var not in variables):
                    variables.append(Literal(var))

    for rule in program.clauses[0]:
        if(rule.getHead()):
            if(rule.getHead() not in S) and (rule.getHead() not in variables):
                variables.append(Literal(rule.getHead()))
        if(rule.getBody()):    
            for var in rule.getBody():
                if (var not in S) and (var not in variables):
                    variables.append(Literal(var))

    for var in variables:
        asp.addVar(PyASP.Variable(var))

    asp.addComment("Afegint alpha rules predicats")
        
    for idx,rule in enumerate(alpha_rules):
        #omitim les rules amb head Q i ~P??
        #if rule.getHead() != q:
        ##print rule
        asp.addComment("              %s" % rule)
        if(rule.getBody()):
            aux="a"+str(idx)
            auxvar=PyASP.Predicate("e",aux,2)
            asp.addPredicate(auxvar)
            r=PyASP.Rule(asp.atomize(rule.getHead()),asp.atomize(rule.getBody())+[auxvar])
            asp.addRule(r)
        else:
            r=PyASP.Rule(asp.atomize(rule.getBody()),asp.atomize(rule.getHead()))
            asp.addRule(r)       
    
    asp.addComment("Afegint strict rules")
    for rule in program.clauses[0]:
        ##print rule.getHead(), rule.getBody()
        if(rule.getBody()!=None):
            r=PyASP.Rule(asp.atomize(rule.getHead()),asp.atomize(rule.getBody()))
            ##print "------>",r
            asp.addRule(r)

    #Start encoding
    #1-.We use direct encoding (walsh), to encode literals from vc
    #already coded in PyASP.write() function
    #2-.We encode rules
    #for rule in asp.rules:
        ##print rule.encode()
    
    asp.addComment("Afegint conflictes")
    asp.addComment("                   %s" % str(variables+predicates.keys()))
    #3-.Check for possible conflicts
    for var in variables+predicates.keys():
        ##print "   - Checking for possible conflicts with "+var+" in set "+str(variables+predicates.keys())+"..."+str(conflicts)
        if var.abs() not in conflicts:
            if var.neg() in variables+predicates.keys():
                c=PyASP.Variable("c"+var.abs())
                asp.addVar(c)
                conflicts.append(var.abs())
                asp.addRule(PyASP.Rule(c,[asp.atomize(var),asp.atomize(var.neg())]))
                ##print PyASP.Rule(c,[asp.atomize(var),asp.atomize(var.neg())])
                asp.addComment("      %s"  % PyASP.Rule(c,[asp.atomize(var),asp.atomize(var.neg())]))
                asp.addRule(PyASP.Rule(PERP,asp.getVar("c"+var.abs())))
                ##print PyASP.Rule(PERP,asp.getVar("c"+var.abs()))
    ##print "Conflict search FINISHED"
    ##print " !! Literals involved in a conlfict:",conflicts
    asp.addComment("                 %s" % conflicts)
    #4-.Encode Warrant and Blocked
    for var in program.get_warranted():
        if var in variables:
            asp.addVar(PyASP.Variable(var))
            a=asp.getVar(var)
            ##print "Warrant:",a,PyASP.Variable(var)
            asp.addComment(var)
            asp.addRule(PyASP.Rule(None,a))
        

    for var in program.get_blocked():
        if var in variables:
            asp.addVar(PyASP.Variable(var))
            a=asp.getVar(var)
#        #print "Blocked:",a
            asp.addComment(var)
            asp.addRule(PyASP.Rule(PERP,a))
    
    #5-.Literal P must be set to True:
    asp.addComment("Literal P must be set to True: %s" % p)
    if p in predicates.keys():
        asp.addRule(PyASP.Rule(PERP,asp.getPredicate(p).neg(1)))
    elif p in variables:
        asp.addRule(PyASP.Rule(PERP,asp.getVar(p).neg()))
    else:
        asp.addVar(PyASP.Variable(p))
        asp.addRule(PyASP.Rule(PERP,asp.getVar(p).neg()))
    #6-. Literal Q, can't be set to True:
    asp.addComment("Literal Q, can't be set to True: %s" % q)
    asp.addComment(predicates.keys())
    if q in predicates.keys():
        asp.addRule(PyASP.Rule(PERP,asp.getPredicate(q).neg(0)))
    sol=asp.solve()

    #check for activated rule

    if sol[0]==True:
        literals_in_rule=[]
        fsol={}
        for i in range(0,len(sol[1])):
            t=re.match("^v\((\d+)\)$",sol[1][i])
            r=re.match("^e\((\d+),(\d)\)$",sol[1][i])
            if t:
                fsol[sol[2][i]]=(t.group(1),True)
            if r:
                if r.group(2) == "1":
                    fsol[sol[2][i]]=(r.group(1),True)
                else:
                    fsol[sol[2][i]]=(r.group(1),False)
        
        for idx,ar in enumerate(alpha_rules):
            activated=False
            if "a"+str(idx) in fsol.keys():
                activated=fsol["a"+str(idx)][1]
            for el in ar[1]:
                if el in fsol.keys():
                    if fsol[el][1]==True and activated==True:
                        activated=True
                    else:
                        activated=False
                else:
                    activated=False
            if activated:
                #print ar[1]
                literals_in_rule+=ar[1]
        program.almostValidCache.insert(p,q,literals_in_rule,True)
        return True
    else:
        program.almostValidCache.insert(p,q,[],False)
        return False

    DEBUG=False
    if(DEBUG):
        ticket=random.randrange(0,1000)
        debFil="%s/encoding%i.debug" % (ENCODINGPATH,ticket)
        while os.path.isfile(debFil):
             ticket=random.randrange(0,100000)
             debFil="%s/encoding%i.debug" % (ENCODINGPATH,ticket)

        #print "          |===> DEBUG in file %s/encoding%i.debug <===|" % (ENCODINGPATH,ticket)
        #print "          |===> ENCODING in file %s <===|" % asp.fil
        #os.system("cat %s   > %s/encoding%i.debug" % (asp.fil,ENCODINGPATH,ticket))
        f=open(debFil,"a")
        f.write("|===> ENCODING in file %s <===|\n" % asp.fil)
        f.write("==============QUERY============\n")
        f.write("almost_validASP(program,%s,%s,%s,level):\n" % (p,q,str(S)))
        f.write("==============SOLUTION============\n")
        #for el in sol:
        #    f.write(str(el)+"\n")
        fsol={}
        if sol[0]==True:
            for i in range(0,len(sol[1])):
                t=re.match("^v\((\d+)\)$",sol[1][i])
                r=re.match("^e\((\d+),(\d)\)$",sol[1][i])
                if t:
                    fsol[sol[2][i]]=(t.group(1),True)
                if r:
                    if r.group(2) == "1":
                        fsol[sol[2][i]]=(r.group(1),True)
                    else:
                        fsol[sol[2][i]]=(r.group(1),False)
            #f.write(str(fsol))
        f.write("\n==============ACTIVATED RULES============\n")
        for idx,ar in enumerate(alpha_rules):
            activated=False
            if "a"+str(idx) in fsol.keys():
                activated=fsol["a"+str(idx)][1]
            for el in ar[1]:
                if el in fsol.keys():
                    if fsol[el][1]==True and activated==True:
                        activated=True
                    else:
                        activated=False
                else:
                    activated=False
            if activated:
                f.write(str(ar)+" a"+str(idx)+" ||||--> Act?: "+str(activated)+" \n")
                #print ar[1]
                #print str(ar)+" a"+str(idx)+" ||||--> Act?: "+str(activated)+" \n"
        f.write("==============ACTIVATED VARIABLES============\n")
        for el in fsol.keys():
            if fsol[el][1]==True and el[0]!="a":
                f.write(el+" -> Active\n")
        #f.write("==============VARIABLES============\n")
        #for el in asp.variables:
        #    f.write(str(el)+"->"+str(asp.variables[el])+"\n")

        ff=open("%s" % asp.fil ,"r")
        aa=[line for line in ff.readlines()]
        a=[]
        for line in aa:
            for el in line.split(" "):
                a.append(el)

        reversedict=dict((str(v[1]),k) for k, v in asp.variables.iteritems())
        ##print  reversedict
        outp=""
        for el in  a:
            t=re.match("(.*)(v\()(\d+)(\))(.*)",el)
            r=re.match("(.*)(e\()(\d+)(,\d\))(.*)",el)
            if t and not r:
                outp+=t.group(1)+" "+t.group(2)+reversedict[t.group(3)]+t.group(4)+" "+t.group(5)
                if re.match(".*\.",t.group(5)):
                    outp+="\n"
            elif r and not t:
                outp+=r.group(1)+" "+r.group(2)+r.group(2)+reversedict[r.group(3)]+r.group(4)+" "+r.group(5)
                if re.match(".*\.",r.group(5)):
                    outp+="\n"
            else:
                outp+=el
        f.write("==============ENCODING============\n")
        #f.write(outp)
        
