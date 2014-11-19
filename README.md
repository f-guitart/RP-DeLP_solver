RP-DeLP_solver
==============

## Introduction

This README explains how to install the RP-DeLP solver in your local machine as well
as the dependencies required. There's a brief explanation of the directory structure
and what main scripts do.

For further explanations or any dectected issue please contact some of the authors:
- guitart.francesc@gmail.com
- ramon@diei.udl.cat
- tracy@diei.udl.cat
- lluis@iiia.csic.cat

## Directory overview:
   * solvers:	This directory contains max-ideal and multiple outputs solvers, as well as
		auxiliar libraries.  
  			 * solvers/debug: this directory contains encodings generated during solving.   		
		If it does not exist will be created automatically.
   * web:	This directory contains scripts for formatting input files. Originally was devoted to
     		read from a web-based application, but now it also converts pdlp files to xml.  
  		     * web/user_submitted_programs: this directory contains xml transformations of input files. 
		If it does not exist will be created automatically.

## Dependencies:
   1. python 2.7
   2. sympy dpll installation (example of installation in Fedora):  
     `#yum install sympy`

   3. Configure rpdelp_web dependency:  
   3.1. Add rpdelp_web.py to pythonpath, example (replace INSTALLATION_PATH for the propper path):  
	`$export PYTHONPATH=$PYTHONPATH:(INSTALLATION_PATH)/web/app/`

   4. Install minisat and clingo:  
      4.1. minisat 2.2.0: http://minisat.se/MiniSat.html  
      4.2. clingo 3.0.5: http://sourceforge.net/projects/potassco/files/clingo/3.0.5/  
      (Note: there should be two links (called clingo and minisat) in your `$PATH`)  

## Examples:
  * There are some pdlp program examples in:  
    http://svn-ccia.udl.cat/argumentation/solvers/examples_clima/
  * Those examples are explained in the following paper:  
    **Web Based System for Weighted Defeasible Argumentation.**  
    *Teresa Alsinet, Ramón Béjar, Francesc Guitart, Lluis Godo.*  
    CLIMA 2013: 155-171
  * Execution arguments:
    The solver is called using solvers/solver.py script. Here is a list of
    execution arguments:
    *  -h,        --help          show this help message and exit
    *  -f FILE,   --file=FILE     reads FILE as input
    *  -x FILE,   --xml=FILE      reads XML FILE as input
    *  -o OUTPUT, --output=OUTPUT output computing options
    *  -s SOLVER, --solver=SOLVER solver to use
    *  -d,        --debug         write debug to PATH (not working)
	      
  * Examples of usage:  
    * `$python solver.py -f examples/program1.pdlp -s minisat -o max-ideal`
    * `$python solver.py -f examples/program1.pdlp -s clingo -o max-ideal`
    * `$python solver.py -f examples/program1.pdlp -s minisat -o multiple`
    * `$python solver.py -f examples/program1.pdlp -s clingo -o multiple`  

## Output format:
After the execution of the script a JSON file should de created. This file will be named using
the following pattern `<original_name>-<output_option>-<solver-option>.json`.
The JSON file contains the following fields:
* file (file solved)
* solver (solver used)
* output (chosen semantics)
* n_outputs (number of outputs)
* timeout (timeout value, not used)
* consistent (true if the strict part of the program is consistent, false otherwise)
* blocked_list (arguments blocked)
* warrant_list (arguments warranted)

The warrant and blocked lists are ordered list containing the arguments warranted and blocked
for each output.

Arguments are formatted as follows:
* Blocked:
  * Conclusion
  * Reason of blocking (cycle or conflict)
  * Conflicting literals or literals involved in the cycle
  * Support
  * Strength
* Warranted:
  * Conclusion
  * Support
  * Strength
   