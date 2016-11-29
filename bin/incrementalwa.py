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

	fname=open(filename,'w')
	path_als = os.path.abspath(alloy_models)
	nodename = platform.node()
	t0 = time.time()
	t_before_xlation = time.time()
	output = als2cnfbed(path_als)
	t_after_xlation = time.time()
	xlation_seconds = t_after_xlation - t_before_xlation
        print 'Time traslation als to cnf:' , xlation_seconds
        
        #ap1.reg('reporte','traslation time: '+str(xlation_seconds)+' ',1)

	path_cnf = output.path_cnf
	path_rels = output.path_rels
        print path_rels
	print("\nParsing {}".format(path_rels))
	rs = Relations(path_rels)
	


	wac_list=[]
        #print("\nCreating native solver instance")
	z = minisat.Zolver()
        rels = rs.rels
        
	#print("Parsing {}".format(path_cnf))
	z.read(path_cnf)
	i=0

        first =True
        while True:
	    if i==cant_max:
		break 

	    inicio = time.time()	
	    verdict = z.solve()
	    tiempo=time.time()-inicio
	    #ap1.reg('reporte', 'Sat '+str(veredict),1)
	    #ap1.reg('reporte','Sat solver time: '+str(tiempo),1)
            print 'sat ',str(verdict) 
            if verdict == True:
	        print 'Sat time: ',tiempo
		i=i+1
                cl = []
		cadelis=''
		fact='<INICIO>fact{ '  
                for j in xrange(len(rels)):
                    r = rels[j]
		    if r.name.find("QF.ac_")==0:
			action= r.name[0:7]
			#print action
                        #para cada varible perteneciente a la relacion QF.ac_ que representa a las acciones  
                        for v in r.vrange:
                            if z.evalmodel(v) == '1':
				value=var2element(v, rs)
				value=value[1:len(value)-1]
				cadelis=cadelis+value+','
				fact=fact + action+'='+value+ ' and '
                                cl = [-v]
		fact=fact[:-5]
		cadelis=cadelis[:-1]
		fact=fact+'}<FINAL>?'+cadelis+'\n'
                z.addclause(cl)
		#almacena fact el wac en un archivo
		print 'wac canditate : ',cadelis
		fname.write(fact)
	
		
		wac_list.append(fact)
            else:
                assert verdict == False, "ERROR: Undefined solver state"
                break
        fname.close()
        return wac_list



def run_alloy(alloy_model):

	path_als = os.path.abspath(alloy_model)
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
	kk = minisat.Zolver()
        rels = rs.rels
	#print("Parsing {}".format(path_cnf))
	kk.read(path_cnf)
	tiempo=time.time()
	veredict = kk.solve()
	tfinal=time.time()-tiempo
	print 'sat time',tfinal
	if not veredict:
		print "Eureka: we found a permanent workaround!!!"
	else: 
		print "the candidate workaround isn't a permanent workaround."
	return veredict







