import os,re, pp_n,time,ConfigParser
from xml.dom import minidom



#-----------------------------------------------------------------------------------------------   
# funcion read_config_case: retorna un diccionario con los valores del archivo config.ini 
#------------------------------------------------------------------------------------------------   
def read_config_case(configfile,section):
    config = ConfigParser.ConfigParser()
    config.read(configfile)
    dict1 = {}
    options = config.options(section)
    for option in options:
        try:
            dict1[option] = config.get(section, option)
            if dict1[option] == -1:
                DebugPrint("skip: %s" % option)
        except:
            print("exception on %s!" % option)
            dict1[option] = None
    return dict1


#--------------------------------------------------------
def time_time(tiempo): #el tiempo viene en forma <nume><s|m>
	res=0
        n=tiempo.split('m')
        if len(n)>1:
		res =int(n[0])*60
        n=tiempo.split('s')
        if len(n)>1:
		res=int(n[0])
        return res 


#--------------------------------------------------------
def textoEnmedio(sCadena, sDelimitador1, sDelimitador2):
      	p=sCadena.find(sDelimitador1)
      	pos2=sCadena.find(sDelimitador2)
	result=''
	if (p!=-1 and pos2!=-1):
      	     result = sCadena[p+(len(sDelimitador1)):pos2]
	return result	

	


def load_pred_aux(archivo):
    f = open(archivo)
    l = f.read()
    return l	


#-----------------------------------------------------------------------------------------------   
# funcion UNSAT: retorna 1 si en f se encuentra el string  'UNSAT'
#		 retorna 0 si en f se encuentra el string  'SAT'
#		 retorna 2 si en f no se encuentra 'SAT' ni 'UNSAT' lo implica que hay Timeout
#------------------------------------------------------------------------------------------------   


def UNSAT(f):
    f = open(f)
    l = f.read()
    if (l.find('UNSAT')>0):
		return 1
    if (l.find('SAT')>0):
		return 0
    if (l.find('Analysis finished')<0):
		return 2


    return

#-----------------------------------------------------------------------------------------   



def save(file_o, file_d):
	ma=open(file_o,"r")
	lineas = ma.readlines()
	ma.close()
	p=open(file_d,'w')
	for linea in lineas:
		p.write(linea)	
	p.close()



                 
	


def generar_cade_para_modelo_als(wac):
	n=1
	cade=''
	for i in wac:
		if n==len(wac):
			cade= cade + 'ac_'+str(n)+'='+i
		else:
			cade= cade + 'ac_'+str(n)+'='+i+' and '
		n=n+1
	cade='not ('+cade+')'
	return cade







def run_modelo_dynalloy(modyn,output,lu):
	os.system('java -jar ../lib/dynalloy4.jar --input ' +modyn+' --output '+output+' --unroll '+lu+' --assertion programa_wap --strictUnroll true  --removeQuantifiers true > sal')
#	os.system('java -jar ../lib/dynalloy4.jar --input ' +modyn+' --output '+output+' --unroll '+lu+' --assertion programa_wap --strictUnroll true   > sal')
        os.system('rm sal')
#########################################################################################################






def run_modelo_alloy_pewa(modalloy,i,unroll,accion,caso,j,to):
    	os.system("timeout "+ to +" java -Xmx8g -Djava.library.path=../lib/amd64-linux/ -jar ../lib/alloycli-1.6.0b3.jar  -s minisat -x uva "+modalloy+" > temp")








	if j==1:
    	   os.system("cp temp ../examples/"+caso+"/results/alt1/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
	if j==2:
    	   os.system("cp temp ../examples/"+caso+"/results/alt2/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
























#########################################################################################################
def run_modelo_alloy(modalloy,i,unroll,accion,caso,j,to):
    	os.system("timeout "+ to +" java -Xmx8g -Djava.library.path=../lib/amd64-linux/ -jar ../lib/alloycli-1.6.0b3.jar  -s minisat -x uva "+modalloy+" > temp")
	if j==1:
    	   os.system("cp temp ../examples/"+caso+"/results/alt1/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
	if j==2:
    	   os.system("cp temp ../examples/"+caso+"/results/alt2/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))

##########################################################################################################







def extraccion__wac(solucion,qf):
  wac=[]
  # se extrae la traza correspondiente al contraejemplo.
  xmldoc = minidom.parse(solucion)
 
  if (not qf):
        lis = xmldoc.getElementsByTagName('skolem')
	for e in lis: 
		if "label" in e.attributes.keys():


                        v = e.attributes["label"].value.strip()	


			if v=="$programa_wap_ac_0" or v=="$programa_wap_ac_1" or v=="$programa_wap_ac_2" or v=="$programa_wap_ac_3" or v=="$programa_wap_ac_4"or  v=="$programa_wap_ac_5" or v=="$programa_wap_ac_6" or v=="$programa_wap_ac_7" or v=="$programa_wap_ac_8" or v=="$programa_wap_ac_9":
				data = e.toxml().split()
                                t = e.getElementsByTagName('atom')[0].toxml()
				accion = pp_n.extraer_bloque(t,'\"','$')
				wac.append(str(accion))
				data = e.toxml().split()

				
				for el in e.getElementsByTagName('atom'):
                                      # t = e.getElementsByTagName('atom')[0].toxml()
                                         
	    		   	       print el.toxml()

				#accion = pp_n.extraer_bloque(t,'\"','$')
				#wac.append(str(accion))
  else:
        
        lis = xmldoc.getElementsByTagName('field')
        for e in lis: 

		if "label" in e.attributes.keys():
                      v = e.attributes["label"].value.strip()	
		      if v=="ac_1" or v=="ac_2" or v=="ac_3" or v=="ac_4" or v=="ac_5" or v=="ac_6" or v=="ac_7" or v=="ac_8" or v=="ac_9" or v=="ac_10":

   			    for el in e.getElementsByTagName('atom'):
                                      # t = e.getElementsByTagName('atom')[0].toxml()#
				   if (el.toxml().find('QF')<0):
					     c=	el.toxml()
	    		   	             ini= c.find('=')+2
	    		   	             fini= c.find('$')
					     c=c[ini:fini].encode('ascii','ignore')
					     wac.append((v+'='+c).encode('ascii','ignore'))

  return wac

def show__wac(wac):
	res=''
	for e in wac:
		res= res +' '+ e  
	res = res + '\n'

	return res	



		     

def expor(nombre,i):
	 
	    f = open('resultado.alsuva', "r")
	    txt=f.read()
	    f.close
	 
    	    f2 = open(nombre+'_'+str(i), "w")
	
            f2.write(txt)	
            f2.close


def rempla(file_name, string_find, string_remplace): 
    f = open(file_name, "r")
    lineas = f.readlines()
    f.close()	
    ma=open(file_name,"w")
    for l in lineas:
	l = l.replace(string_find,string_remplace) 
	ma.write(l)
    ma.close()	
#########################################################################################################

def reg(archi,linea,i):
	if i==0:
    	   os.system('echo "'+linea+'" > '+archi)
	else:
	   os.system('echo "'+linea+'" >> '+archi)
#######################################################################################################

def borrar_pre(file_name):
    f = open(file_name, "r")
    lineas = f.readlines()
    f.close()	
    ma=open(file_name,"w")
    for l in lineas:
	prim=''
	rest=''
	i=l.find("fact{QF.thisType_")
	if i>=0:
	     prim =l[:i]			
	     rest=l[i:]
	     j=rest.find('}')
	     rest=rest[j+1:]
	     l = prim+rest			
	ma.write(l)
    ma.close()


#########################################################################################################
def mostrar_programa(metodo_roto,wac,archi,perfiles):
	
#perfiles es un diccionario perfiles[accion]=['']

# para cada accion guardada en wac, buscar los parametros que tiene en perfiles[accion], luego para cada uno de estos parametros buscar su vaor en archi. hay que tener en cuenta que la accion que esa en la posicion 0 va a tener que buscar los parametros den archi con parametro_1. 
# puede servir una funcion auxiliar de busqueda(parametro) return valor. ej
# nota: buscar el parametro y luego el segundo valor del atom

#<field label="element_1" ID="72" parentID="54">
#   <tuple> <atom label="QF$0"/> <atom label="-1"/> </tuple>
#   <types> <type ID="54"/> <type ID="1"/> </types>
#</field>

 perfil= perfiles[metodo_roto]     
 k=len(perfil)
 cade=''
 for p in range(1,k):	
    pc=perfil[p]+'_0'

    cade=cade+ buscar_valor('resultado.alsuva',pc)+','



 cade=cade[:-1]
 parametros_actuales=metodo_roto+'('+cade+')'
 print 'Metodo roto:'
 print parametros_actuales 
 parametros_actuales='' 
 print 'Workaround candidato'
 for ac in wac:
   c=ac.find('=')
   ac=ac[c+1:]	
   nac=1	
   perfil= perfiles[ac]     
   
   k=len(perfil)
   for p in range(1,k):	
	pc=perfil[p]+'_'+str(nac)
	parametros_actuales=parametros_actuales+ buscar_valor('resultado.alsuva',pc)+','
   print ac+'('+parametros_actuales[:len(parametros_actuales)-1]+')'	



#f=listar_metodos_tipos('../input/examples/src/Lista.java')
#print f


def buscar_valor(solucion,valor):
  xmldoc = minidom.parse(solucion)
  s=''	
  for n in xmldoc.getElementsByTagName("field"):
    #print n.attributes["label"].value

	if (n.attributes["label"].value==valor):
	     s=n.childNodes[1].toxml()
	     n=s.find('/>')	
	     if (n>0):
			s=s[n:]
	   	        n=s.find('=')	
			s=s[n+2:]
			n=s.find('"')
			s=s[:n]
			break
  return s




#perfil retorna un diccionario con ek nombre del metodo como clave y el valor asociado es una lista con el retorno y los parametros
def perfil_ok(archi):
	    d={} 	
	    f = open(archi, "r")
	    t=f.read()
    	    f.close()
	    i=0	
	    	
	    while True:
		i=t.find('retorno=')
		if i!=-1:
		       t=t[i+8:]
		       j=t.find('*')  		
		       ret=t[:j]
		       lista=[ret]	
		       met=pp_n.textoEnmedio(t,'/','(')	 
		       met=met.strip()
   		       parametros=pp_n.textoEnmedio(t,'(',')')	 
		       id_parametros= parametros.split(',')


		       for m in id_parametros:
				m=m.strip()
				m = m.split(' ')
				if (len(m)>1):
				    lista.append(m[0].strip())
				    lista.append(m[1].strip())
		       d[met]=lista
		   		   
		else:
		   break
            return d



def tc(perfiles,tipos_simples):
   	
  elementos = perfiles.keys()
  res=[]
  for met in elementos:
       e=perfiles[met]	
       if not (e[0] in tipos_simples): 
		res.append(e[0])		
#       del e[:1]        		
       if len(e)==1:
		continue	
       if (len(e)>1): 
	     for i in xrange(1,len(e),2):
  	         if not (e[i] in tipos_simples):
 		      res.append(e[i])
	
  
  return list(set(res))


def tipos_compuestos(lista_tipos_compuestos):
  res=''	
  for e in lista_tipos_compuestos:
       res=res+'set_'+e+': set '+e+', '
  return res

	    


def bin_to_int(s):
	s=s[s.find('fact'):]
	l=s.split('and')
	res=''
	for e in l:
		d=e.split('=')	
		d[1]=d[1].strip()
		if(d[1]=='true'):
			res='1'+res
		else:
			res='0'+res

	return str(int(str(res),2))

def bin_to_int_old(s):
	s=s[s.find('fact'):]
	l=s.split('and')
	res=''
	for e in l:
		d=e.split('>')	
		d[1]=d[1].strip()
		if(d[1]=='true'):
			res='1'+res
		else:
			res='0'+res

	return str(int(str(res),2))

#-----------------------------------------------------------------

def conv_time(num):
	hor=(int(num/3600))  
	minu=int((num-(hor*3600))/60)  
	seg=num-((hor*3600)+(minu*60))
	return str(hor)+" h "+str(minu)+" m "+str(seg)+" s"



def dec_to_int3(x,v):
  k=0
  i=1
  s=0
  dec=x
  l=[]
  while dec>0:
      if k<0:	
	  temp=v+'.b0'+str(k)+'='
      else:
	 temp=v+'.b'+str(k)+'='
      rem=dec%2
      if rem==0:
	    temp=temp+'false'
      else:
	    temp=temp+'true'
      l.append(temp)
     
      
      s=s+(i*rem)
      dec=dec/2
      i=i*10
      k=k+1
  for i in range(k,32):
      if k<0:	
	  temp=v+'.b0'+str(k)+'='
      else:
	 temp=v+'.b'+str(k)+'='
      temp=temp+'false'
      l.append(temp)
      k=k+1
  return 'fact{\n'+'\n'.join(l)+'\n}\n'




def isto(d):
	os.system("echo $? >> kkk")
	return

isto(4)








