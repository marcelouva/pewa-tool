import alloy
from alloy.cli import als2cnfbed
from alloy.relations import Relations
from alloy.kodkod import Relation
from minisat import minisat
import sys, os, platform
import time
import logging
#Log  = logging.getLogger(__name__)


def var2tuple(var, rs):
    (rel_i, (atom_i0, atom_i1)) = rs.v2rt[var]
    res = "(" + rs.ind2an[atom_i0] + "," + rs.ind2an[atom_i1] + ")"
    return res


def var2element(var, rs):
    (rel_i, atom_i0) = rs.v2rt[var]
    res = "(" + rs.ind2an[atom_i0[0]] + ")"
    return res

#
def run_incremental_alloy(alloy_models,cant_max,filename):

	output=open(filename,'w')
		
	
	path_als = os.path.abspath(alloy_models)


	nodename = platform.node()
	
	t0 = time.time()

	t_before_xlation = time.time()
	output = als2cnfbed(path_als)
	t_after_xlation = time.time()
	xlation_seconds = t_after_xlation - t_before_xlation
        print 'Time traslation als to cnf:' , xlation_seconds
	

	path_cnf = output.path_cnf
	path_rels = output.path_rels

	print("\nParsing {}".format(path_rels))
	rs = Relations(path_rels)
	


	wac_list=[]
        #print("\nCreating native solver instance")
	z = minisat.Zolver()
        rels = rs.rels
	#print("Parsing {}".format(path_cnf))
	z.read(path_cnf)
	i=0
        while True:
	    if i==cant_max:
		break
	    verdict = z.solve()
            if verdict == True:
		i=i+1
                #print("\nSAT")
                cl = []
		fact='<INICIO>fact{ '  
                for j in xrange(len(rels)):
                    r = rels[j]
		    if r.name.find("QF.ac_")==0:
			action= r.name[0:7]
                        #para cada varible perteneciente a la relacion QF.ac_ que representa a las acciones  
                        for v in r.vrange:
                            if z.evalmodel(v) == '1':
				value=var2element(v, rs)
				value=value[1:len(value)-1]
				
				fact=fact + action+'='+value+ '\n'
                                #print v, " : ", var2element(v, rs)
                                cl = [-v]
		fact=fact+'}<FINAL>\n'
                z.addclause(cl)
		#almacena fact el wac en un archivo
		output.write(fact)
		wac_list.append(fact)
            else:
                assert verdict == False, "ERROR: Undefined solver state"
                break
        output.close()
        return wac_list



