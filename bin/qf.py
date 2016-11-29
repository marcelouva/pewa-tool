
import os

def rempla(file_name, string_find, string_remplace): 
    f = open(file_name, "r")
    lineas = f.readlines()
    f.close()	
    ma=open(file_name,"w")
    for l in lineas:
	l = l.replace(string_find,string_remplace) 
	
	ma.write(l)
    ma.close()	





def gen_fact_qf(loops,accion):
    os.system('grep ADD_QF resultado.als > s_a')
    os.system('grep FACT resultado.als >> s_a')


    f = open('s_a', "r")
    lineas = f.readlines()
    f.close()	
    for l in lineas:
      i=l.find('ADD_QF')
      if(i>0):
	   l=l[8:]
           ini=0
	   fin=loops
		 
	   for i in range(ini,fin):
                nl=l
	   	if (l.find('i+1')>0):
			nl = l.replace('<i+1>',str(i+1))	
	   	nl = nl.replace('<i>',str(i))
                rempla('resultado.als','one sig QF {','one sig QF {'+nl)


      i=l.find('FACT')
      if(i>0):
            
	   l=l[6:]
           #esto es para generar las variables de los fact. hay diferencia entre la accion a reparar y las que se usan para reparar
           #print l
           f= l.find(accion+'_')
           ini=0
	   fin=loops
           #insertar l al final del archivo resultado.als 
           for i in range(ini,fin):
                nl=l
		if (l.find('i+1')>0):
			nl = l.replace('<i+1>',str(i+1))
   		nl = nl.replace('<i>',str(i)) 		
	                 
		os.system("echo '"+nl+"' >> resultado.als")
    os.system('rm s_a')

#main(1,'TimeOfDay_minusHours')




