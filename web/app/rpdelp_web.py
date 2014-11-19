import sys, os
import re
import datetime
from xml.etree.ElementTree import Element, SubElement, Comment, tostring
import socket
from random import randrange

if socket.gethostname()=="kvothe" or socket.gethostname()=="lloyd" or socket.gethostname()=="ideafix":
    HOMEPATH="/home/francesc/doctorat/argumentation/web"
    FILEPATH=HOMEPATH+"/user_submitted_programs/"
elif socket.gethostname()=="arinf.udl.cat":
    HOMEPATH="/home/francesc/argumentation/web"
    FILEPATH=HOMEPATH+"/user_submitted_programs/"

elif re.match("compute-\d+-\d+\.local", os.uname()[1]):
    HOMEPATH="/state/partition1/"
    FILEPATH=HOMEPATH+"/user_submitted_programs/"
    if not os.path.isdir(FILEPATH):
        os.system("mkdir %s" % FILEPATH)

else:
    HOMEPATH="/home/francesc/doctorat/argumentation/web"
    APPPATH=os.path.realpath(__file__)
    print APPPATH
    t=re.match('(.*)app/rpdelp_web.py',APPPATH)
    if t:
        WEBPATH=t.group(1)
    FILEPATH=WEBPATH+"/user_submitted_programs/"

if not os.path.exists(FILEPATH):
    os.makedirs(FILEPATH)

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
    

def validate_level(level_as_string):
#takes a level as string, and return a tuple (bool,list).if bool true, the level has been validate
#else list return bad formed formulas

    bad_clauses=[]
    good_clauses=[]
    is_good=True
    for clause in [c+"." for c in level_as_string.split(".") if c != "\n"]:
        re.sub(ur'\n','', clause)
        t2=re.match("\s\s\.",clause)
        is_blank=len(clause)<2 or t2

        if not is_blank:
            #clause=f.group(1)
            try: Clause(clause)
            except:
                is_good=False
                bad_clauses.append(clause)
            else:
                good_clauses.append(clause)
    if is_good:
        return is_good,good_clauses
    else:
        return is_good,bad_clauses




def generate_xml(strict_level,def_levels):
    root = Element('rpdelp')
    strict_lvl=SubElement(root,'strict_level')
    for clause in strict_level:
        c=SubElement(strict_lvl,'clause')
        c.text=clause

    for idx,level in enumerate(def_levels):
        def_lvl=SubElement(root,'defeasible_level',{'alpha': str(idx)})
        for clause in level:
            c=SubElement(def_lvl,'clause')
            c.text=clause
        
    return root

def save_xml(xml_file):
    
    file_name=FILEPATH+"/rpdelp-web-"+datetime.datetime.now().strftime("%d%m%Y%H%M%S")+str(randrange(1000))+".xml"

    f=open(file_name,"w")
    f.write(tostring(xml_file))
    f.close()
    return file_name

def delete_xml(file_path):
    os.system("rm %s" % file_path)

def output_xml(stats,output):
     root = Element('rpdelp-result')
     statistics=SubElement(root,'stats')
     outputs=SubElement(root,'outputs')

     for el in output:
         o=SubElement(outputs,'output')
         warr=SubElement(o,'warrants')
         for lit in el[0]:
              l=SubElement(warr,'literal')
              l.text=lit
         block=SubElement(o,'blocked')
         for lit in el[1]:
              l=SubElement(block,'literal')
              l.text=lit

     return root

def output_html(stats):
    #table="<table><tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>" % ("Output","Warrants","Bolcked","Stats")
    if stats["consistent"]==False:
        return "<p> Inconsistent strict knowledge</p>"
    table=""
    #llista de garantits per nivells
    warr_list=stats["warrant_list"]
    #llista de garantits per nivells
    block_list=stats["blocked_list"]
    #nombre de sortides
    total_outputs=stats["n_outputs"]
    times=stats["times"]

    print total_outputs
    html_outputs=[]
    for n_output in range(0,total_outputs):
        w_html=""
        b_html=""
        s_html=""
        for warrant in warr_list[n_output]:
            print warrant
            if warrant[2]==0:
                level="strict"
            else:
                level=warrant[2]
            w_html+="<p>%s: %s [%s]</p>" % (warrant[0],warrant[1],level)
        for blocked in block_list[n_output]:
            b_html+="<p>%s: %s(%s) [%s]</p>" % (blocked[0],blocked[1],blocked[2],blocked[4])
        for blocked in block_list[n_output]:
            s_html+="<p>%s: %s</p>" % (blocked[0],blocked[3])
        time=times[n_output-1]

        html_output="<tr>\
                      <td>%s</td>\
                      <td>%s</td>\
                      <td>\
                      %s\
                      </td>\
                      <td>\
                      %s\
                      </td>\
                      <td>\
                      %s\
                      </td>\
                      <td>\
                      %s\
                      </td></tr>" % (total_outputs,n_output+1,w_html,b_html,s_html,time)
        html_outputs.append(html_output)

    for o in html_outputs:
        table+=o

    return table

if __name__=="__main__":
   
    w=[[("a1","b1","1"),("a2","b2","1"),("a3","b3","1")],[("c1","d1","1"),("c2","d2","1"),("c3","d3","1")]]
    b=[[("A1","B1","1"),("A2","B2","1"),("A3","B3","1")],[("C1","D1","1"),("C2","D2","1"),("C3","D3","1")]]
    t=["1","2"]

    stats={}
    stats["n_outputs"]=2
    stats["warrant_list"]=w
    stats["blocked_list"]=b
    stats["times"]=t

    print output_html(stats)

    out_html="<table><col width=\"7\%\" /><col width=\"7\%\" /><col width=\"25\%\" /><col width=\"25\%\" /><col width=\"25\%\" /><col width=\"10\%\" /><tr><td><b>Number of outputs</b></td><td><b>Output</b></td><td><b>Warranted conclusions</b></td><td><b>Bolcked conclusions</b></td><td><b>Support of bolcked conclusions</b></td><td><b>Time</b></td></tr>"
    out_html+=output_html(stats)
    out_html+="</table>"

    f=open("prova.html","w")
    f.write(out_html)
    f.close()
