#!/bin/python
import sys,os,re


PERP="Perp"

class NumVar:
    def __init__(self):
        self.numvars=0
    def __iter__(self):
        return self.numvars
    def next(self):
        self.numvars+=1
        return self.numvars
    def actual(self):
        return self.numvars

class Predicate(tuple):
    def __new__(cls,pred,var,dom):
        return tuple.__new__(cls,(pred,Variable(var),dom))
    
    def encode(self,*args):
        if args:
            val=args[0]
        else:
            val=1
        return self.getPred()+"("+self.getVar().getNumVar()+","+str(val)+")"

    def getPred(self):
        return self[0]

    def getVar(self):
        return self[1]
    
    def getDom(self):
        return self[2]
    
    def encodeDomain(self):
        return [self.getPred()+"("+str(self.getVar()[1])+","+str(val)+")" \
                    for val in range(0,self.getDom())]

    def neg(self,*args):
        if args:
            val=args[0]
        else:
            val=1
        #print "***************"+self.encode(val)
        return "not "+self.encode(val)

class Variable(tuple):
    def __new__(cls,var):
        return tuple.__new__(cls,(var,numvar.next()))

    def getNumVar(self):
        return str(self[1])
    
    def getVar(self):
        return self[0]

    def encode(self):
        return "v("+self.getNumVar()+")"

    def neg(self):
        return "not "+self.encode()

class Comment(str):
    def __new__(cls,text):
        return str.__new__(cls,text)  

    def encode(self):
        return "%*"+self+"*%"

class Rule:
    def __init__(self,head,body):
        self.head=[]
        self.body=[]
        if type(head) == list:
            for lit in head:
                self.head.append(head)
        else:
            self.head=[head]

        if type(body) == list:
            self.body=body
        else:
            self.body=[body]

    def getHead(self):
        return self.head

    def getBody(self):
        return self.body

    def encode(self):
        #print self
        r=""
        if self.getHead() != [None]:
            if self.getHead()[0]!=PERP:    
                r=r+self.getHead()[0].encode()+" "
                for lit in self.getHead()[1:]:
                    r=r+","+lit.encode()+" "
            r=r+":- "

        r=r+self.getBody()[0].encode()
        for lit in self.getBody()[1:]:
            r=r+" ,"+lit.encode()
        return r+"."

    def __repr__(self):
        return str(self.getHead())+str(self.getBody())
   
class CardinalityRule(Rule):
    '''Suposo que no es la millor manera de fer herencia
    no en se mes
    TODO: Revisa aixo analfabet!'''

    def __init__(self,head,body,card):
        self.r=Rule(head,body)
        self.head=self.r.getHead()
        self.body=self.r.getBody()
        self.card=card

    def encode(self):
        r=""
        if self.getHead() != [None]:
            if self.getHead()[0]!=PERP:    
                r=r+self.getHead()[0].encode()+" "
                for lit in self.getHead()[1:]:
                    r=r+","+lit.encode()+" "
            r=r+":- "
        
        r=r+"1{"+self.getBody()[0].encode()
        for lit in self.getBody()[1:]:
            r=r+" ,"+lit.encode()
        return r+"}." 

class ProgramASP(object):
    def __init__(self,*args):
        self.predicates={}
        self.variables={}
        self.rules=[]
        self.fil=ENCODINGPATH+"/"+self.__getFilename__(args[0])


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

    def addVar(self, var):
        if var[0] not in self.variables.keys():
            self.variables[var[0]]=var

    def getVar(self, varName):
        try:
            return self.variables[varName]
        except KeyError:
            return None

    def getVarByNum(self,num):
        return [item[0] for item in self.variables.items() if item[1][1] == num]

    def addPredicate(self, pred):
        if pred[1][0] not in self.variables.keys():
            self.addVar(Variable(pred[1][0]))
        self.variables[pred[1][0]]=pred[1]
        self.predicates[pred[1][0]]=pred

    def getPredicate(self,var):
        try:
            return self.predicates[var]
        except KeyError:
            return None
    
    def addRule(self, r):
        self.rules.append(r)

    def addComment(self,comment):
        self.rules.append(Comment(comment))

    def encode(self):
        if len(self.rules)>0:
            return [rule.encode() for rule in self.rules]
        else:
            pass
    
    def atomize(self,lit):
        if type(lit) == list:
            return [self.atomize(var) for var in lit]
        if lit in self.predicates.keys():
            return self.predicates[lit]

        elif lit in self.variables.keys():
            return self.variables[lit]

        else:
            return None

    def write(self):

        filOut=open(self.fil,"w")
        #encode using direct encoding
        for pred in self.predicates.keys():
            #print self.predicates[pred]
            rang="["
            rang=rang+self.predicates[pred].encodeDomain()[0]
            for el in self.predicates[pred].encodeDomain()[1:]:
                rang=rang+", "+el
            rang=rang+"]."
            filOut.write("1 #max "+rang+"\n")
            filOut.write(":- not "+self.predicates[pred].encodeDomain()[0])
            for el in self.predicates[pred].encodeDomain()[1:]:
                filOut.write(", not "+el)
            filOut.write(".\n")
            filOut.write(":- 2 {"+self.predicates[pred].encodeDomain()[0])
            for el in self.predicates[pred].encodeDomain()[1:]:
                 filOut.write(", "+el)
            filOut.write("}.\n")
            #filOut.write("1 #min "+rang+"\n")

        #print self.encode()
        for r in self.encode():
            filOut.write(str(r)+"\n")
        filOut.close()

    def solve(self):

        self.write()
        os.system("%sclingo %s > %s.sol" % (CLINGOPATH,self.fil,self.fil))
        f=open("%s.sol" % self.fil , "r")
        sol=[line for line in f.readlines()]
        DEBUG=True
        if not DEBUG:
            os.system("rm %s.sol" % self.fil)
            os.system("rm %s" % self.fil)
        litsol=[]

        if sol[0] == 'UNSATISFIABLE\n':
            return (False,None,sol[2])
        elif sol[2] == 'SATISFIABLE\n':
            m=re.match("^Time.*:.*(\d+\.\d+)\n$",sol[5])
            if(m):
                time=m.group(1)
            else:
                time=None
            
            for el in sol[1].split(" "):
                m=re.match("[a-zA-Z]*\((.*[\s.*]*)\)$",el)
                if(m): 
                    litsol+= self.getVarByNum(int(m.group(1).split(",")[0]))
            return (True,sol[1].split(" "),litsol,time)        

        
            
numvar=NumVar() 
if __name__ == '__main__':
    
    asp=ProgramASP("enc.asp")
    a=Predicate("e","a",2)
    b=Variable("b")
    c=Variable("c1")
    asp.addPredicate(a)
    asp.addVar(b)
    r1=Rule(a,b)
    r2=Rule(None,b)
    r3=Rule(PERP,c.neg())
    asp.addRule(r1)
    asp.addRule(r2)
    #asp.addRule(r3)
    #print asp.solve("enc.asp")
