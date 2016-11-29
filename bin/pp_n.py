#!/usr/bin/python
import os,sys
def textoEnmedio(sCadena, sDelimitador1, sDelimitador2):
      	p=sCadena.find(sDelimitador1)
      	pos2=sCadena.find(sDelimitador2)
	result=''
	if (p!=-1 and pos2!=-1):
      	     result = sCadena[p+(len(sDelimitador1)):pos2]
	return result	


def p_params(cade,hp):
	k=cade.split(',')
	for e in k:
		c=e.split(':')
		hp[c[0].strip()]=c[1].strip()
	


def p_p(hp):
	res=''
	for key, value in hp.iteritems():
	    k = key
	    v = value
	    res= res + ','+ k +':' + v  
        return res[1:]


def minBitwidthToRepresent(size):
        k = 1;
	while True:
		if (size>pow(2,k)/2-1):
			k=k+1;
		else:
		  	return k;
	




# extrae un bloque de codigo balanceado, a y c deben ser carcteres 
def extraer_bloque(cade,a,c):
      	p=cade.find(a)
        cade=cade[p+1:] 
	cant=1
	nc=''	
	for e in cade:
		if e==a:
			cant=cant+1
		if e==c: 
			cant=cant-1
			if cant==0:
     		   	     break;	
		nc=nc+e			
	return nc

def del_bloque(cade,a,c):
	res= extraer_bloque(cade,a,c)	
        nc=cade[cade.find(res)+len(res)+1:] 
	return nc


def nf(sCadena, sDelimitador2):
      	return(sCadena.find(sDelimitador2))

def normalizar_nombres_pred(texto,method_to_check):
	lista=[]
	copia=texto	
	while True:
		res = textoEnmedio(texto,"pred","[")
		if (res!=''):
			res=res.strip()
			lista.append([res,res+'_'+method_to_check])
			texto= del_bloque(texto,'[',']')
			texto= del_bloque(texto,'{','}') 

		else: 
		  break
	for m in lista:
		copia = copia.replace(m[0],m[1])
	return copia
	



#si i==1 se genera el codigo del programa y en tipos_no_simples estan los tipos no simples que va a tomar como parametros que tienen que tener sets.
def gen_code(retorno,archivo_dals, method_to_check,i,salida_dals,parametros_programa,planti,tipos_no_simples):
	# agregar un if retorno==X por cada tipo de retorno posible del programa java. ver 
	print retorno
	if retorno=='I':
		 	os.system('sed -i s/return/return_int/g '+ archivo_dals)
	if retorno=='B':
	 	os.system('sed -i s/return/return_bool/g '+ archivo_dals)
	if retorno=='TS':
	 	os.system('sed -i s/return/return_TS/g '+ archivo_dals)
	if retorno=='Lista':
	 	os.system('sed -i s/return/return_Lista/g '+ archivo_dals)
	if retorno=='LNode':
	 	os.system('sed -i s/return/return_LNode/g '+ archivo_dals)



	f = open(archivo_dals, "r")
        archi =open(salida_dals,'a')
        planti=open('plantilla','a')
        salida=open('plantilla','a')

	texto = f.read()

	texto=normalizar_nombres_pred(texto,method_to_check)
	accion=[]
	invariantes=[]
	aux=''
	b=1
	while True:

		name_pred = textoEnmedio(texto,"pred","[").strip()
		if name_pred=='':	
			break
		b=False
		if name_pred.find('invariant') >=0:
                          b=True 

		archi.write('\npred '+name_pred+' \n')
		planti.write('\npred '+name_pred+' \n')
		parametros_pred = extraer_bloque(texto,'[',']')
                if b:
			invariantes.append(name_pred+'['+extraer_parametros_reales(parametros_pred) +']') 



       	        texto = del_bloque(texto,'[',']')
		
		



    	        if (name_pred.find('postcondition')!=-1 or name_pred.find('precondition')!=-1  ) and (i==1):
			if retorno=='I':
				parametros_pred = 'validint:boolean, '+parametros_pred
			if retorno=='B':
				parametros_pred = 'validbool:boolean, '+parametros_pred

		archi.write('['+parametros_pred+']'+'\n') 
		planti.write('['+parametros_pred+']'+'\n') 


		cuerpo_pred = extraer_bloque(texto,'{','}')

		if name_pred.find('precondition')!=-1 and i==1:
 
		       if retorno=='I':

				cuerpo_pred= 'equ[validint,false] and '+cuerpo_pred
		       if retorno=='B':
				cuerpo_pred= 'equ[validbool,false] and '+cuerpo_pred


                aux =cuerpo_pred  



    	        if name_pred.find('postcondition')!=-1  and i==1:
			if retorno=='I':
			     cuerpo_pred=" not(equ[validint,true] and "+cuerpo_pred+')'
			if retorno=='B':
			     cuerpo_pred=" not(equ[validbool,true] and "+cuerpo_pred+')'
			if retorno=='V':
			     cuerpo_pred='not('+cuerpo_pred+')'
			if retorno=='LNode':
			     cuerpo_pred='not( some ln: LNode | ln in set_LNode && ln=return\' && '+cuerpo_pred+')'
			if retorno=='TS':
			     cuerpo_pred='not( some ln: TS | ln in set_TS && ln=return\' && '+cuerpo_pred+')'
			if retorno=='Lista':
			     cuerpo_pred='not( some ln: Lista | ln in set_Lista && ln=return\' && '+cuerpo_pred+')'




		#aca6 si el retorno no es un tipo simple por ejemplo TreeSet
		# deberia agregarse algo como 
		#     not (some ts:TreeSEt | ts perteneza a set_TS y cumpla con la pos del programa roto




		planti.write('{'+aux+'}'+'\n')  
		archi.write('{'+cuerpo_pred+'}'+'\n')
		
      	        texto = del_bloque(texto,'{','}')

	name_action = textoEnmedio(texto,"program","[").strip()


	parameters_action = extraer_bloque(texto,'[',']')

        p_params(parameters_action,parametros_programa)

   	texto = del_bloque(texto,'{','}')		
	parametros_asercion = extraer_bloque(texto,'[',']')
       	texto = del_bloque(texto,'[',']')
	
	res = extraer_bloque(texto,'{','}')



	pre = extraer_bloque(res,'{','}')






       	res = del_bloque(res,'{','}')		
	cade = extraer_bloque(res,'{','}').strip()[4:]
       	res = del_bloque(res,'{','}')		




        post = extraer_bloque(res,'{','}')


	if i==-1:
		archi.write('act '+name_action+'\n') 
		planti.write('act '+name_action+'\n') 

		archi.write('['+parameters_action +']'+'\n')
		planti.write('['+parameters_action +']'+'\n')

		archi.write('{  pre {'+pre+'}'+'\n') 
		planti.write('{  pre {'+pre+'}'+'\n') 

		archi.write('   post {'+post+'}}'+'\n')
		planti.write('   post {'+post+'}}'+'\n')  

		accion.append([method_to_check,cade])	
	if i==0:
		archi.write('act '+name_action+'\n') 
		planti.write('act '+name_action+'\n') 

		archi.write('['+parameters_action +']'+'\n')
		planti.write('['+parameters_action +']'+'\n')

		archi.write('{  pre {'+pre+'}'+'\n') 
		planti.write('{  pre {'+pre+'}'+'\n') 

		archi.write('   post {'+post+'}}'+'\n')
		planti.write('   post {'+post+'}}'+'\n')  

		accion.append([method_to_check,cade])	

	# i==1 genera el programa 
	#aca6 vero como cambiar la post del programa teniendo en cuenta que en post viene la post del metodo roto
	#
	if (i==1):
		if retorno=='I':
   		      pre=pre.replace('[','[validint, ',1 )
   		      post=post.replace('[',"[validint', ",1 )
		if retorno=='B':
   		      pre=pre.replace('[','[validbool, ',1 )
		      post=post.replace('[',"[validbool', ",1 )
				




		
		
		pp = 'assertCorrectness programa_wap ' + '[\n '+tipos_no_simples+'validint:boolean, validbool:boolean, ac:actionExec,' +p_p(parametros_programa)+ ']{'
                pp = pp +'pre={'+pre+'}   __wap__   post={'+post +'}}'   
		texto= texto[nf(texto, "assertCorrectness"):]
		accion.append(['programa',pp])
	archi.close()







	planti.close()
	return accion








def gen_prog(clase,metodos,programa,d):
        archi=open('inicio.dals','w')
	archi.write('sig '+ clase +' extends java_lang_Object {}{}\n') 
	archi.write('abstract sig actionExec{}\n') 
	cade = 'one sig name_ac extends actionExec{}\n'
	prg=[]
        for a in metodos:
	    archi.write(cade.replace('name_ac',a[0])) 
	    if d[a[0]]=='I':
	            prg.append(' ('+a[1]+'; '+ 'ac:='+a[0]+';validint:=true) ')
	    if d[a[0]]=='B':
	            prg.append(' ('+a[1]+'; '+ 'ac:='+a[0]+';validbool:=true) ')
	    if d[a[0]]=='V':
	            prg.append(' ('+a[1]+'; '+ 'ac:='+a[0]+')')

	p = '\nprogram={\n( '



	for i in range(0,len(prg)):
	   if i==len(prg)-1:	
		    p = p + prg[i]+'\n)*}'	
	   else: 
		    p = p + prg[i]+'\n' +'+'+'\n'
	print '_______________________________'        
	print p
	print '_______________________________'        



	programa=programa.replace('__wap__',p)
	archi.write(programa)
	archi.write('\ncheck programa_wap\n')
	archi.close()


def gen_prog_plant(clase,metodos,programa):
        archi=open('inicio_v.dals','w')
	archi.write('\nsig '+ clase +' extends java_lang_Object {}{}\n') 
	archi.write('abstract sig actionExec{}\n') 
	cade = 'one sig name_ac extends actionExec{}\n'
	prg=[]
	#print metodos
	#sys.exit(0)
        for a in metodos:
	    archi.write(cade.replace('name_ac',a[0])) 
            prg.append(' ('+a[1]+'; '+ 'ac:='+a[0]+') ')

	p = '\nprogram={\n(\n __uva__ \n )}'
	programa=programa.replace('__wap__',p)
	archi.write(programa)
	archi.write('\ncheck programa_wap\n')
	archi.close()




def gpw(lis_wac,metodos):
       
	prg=[]
	for o in lis_wac:
		call = busca_call(o,metodos)
       	        prg.append(call)
        p=''
	for i in range(0,len(prg)):
    

           if i==len(prg)-1:	
        	    
		    p = p + prg[i]+'\n'	
	   else: 
		   
		    p = p + prg[i]+'\n' +';'+'\n'

        f = open('PLANTILLA.dals', 'r')	
	s = f.read()
	f.close()
	s = s.replace('__uva__',p)
        r = open('wac_candidato.dals', 'w')	
	r.write(s)
	r.close()
















def busca_call(n, lista):
	for e in lista:
			
		if n==e[0]:
		      return e[1]
		      break



# lista tiene la lista donde se encuentra el wac
# metodos es la lista que retorna gencode
# postcond_wac es la llamada del predicado posta
#

def gen_vefir_wac(lista, metodos, programa,postcond_wac):
	prg=[]
	call=''
	programa=''
	for o in lista:
		call = busca_call(o,metodos)
                prg.append(call)
	
	p = '\nprogram={\n( '
	for i in range(0,len(prg)):
	   if i==len(prg)-1:	
		    p = p + prg[i]+'\n)}'	
	   else: 
		    p = p + prg[i]+'\n' +';'+'\n'
	

	programa=programa.replace('__wap__',p)
	
	j=programa.find('post={')
	aux=programa[j:]
        aux = extraer_bloque(aux,'{','}')
	programa=programa.replace(aux,postcond_wac)
	print programa
	


def extraer_parametros_reales(params):
	cade=params+','
	res=''
	while cade.find(':')>=0:
		 res=res+extraer_bloque(cade,',',':').strip()+','	
	         cade=del_bloque(cade,',',':')
		 
        return res[:-1]
	





def gen_code_n(retorno,archivo_dals,metodo):
   if retorno=='I' or retorno=='B':	
	f = open(archivo_dals, "r")
	texto = f.read()
	f.close()
	i=texto.find(metodo)
	if i!=-1:	
	     ant=texto[:i+len(metodo)]
	     post=texto[i+len(metodo):]	
             if retorno=='I':
	             post= post.replace('[','[validint:boolean,',1)
   	             post= post.replace('{',' { equ[validint,false] and ',1)
		     i=post.find(metodo)
	    	     if i!=-1:	
	     		pos_1=post[:i+len(metodo)]
	     		pos_2=post[i+len(metodo):]
  	                pos_2 = pos_2.replace('[','[validint,',1)

	     if retorno=='B':
	             post= post.replace('[','[validbool:boolean,',1)		   
       	             post= post.replace('{',' { equ[validbool,false] and ',1)
		     i=post.find(metodo)
	    	     if i!=-1:	
	     		pos_1=post[:i+len(metodo)]
	     		pos_2=post[i+len(metodo):]
  	                pos_2 = pos_2.replace('[','[validbool,',1)

	f = open(archivo_dals, "w")
	f.write(ant+pos_1+pos_2)
	f.close()


def gen_prog_ok(clase,metodos,programa,d,tipos_comp):
        archi=open('inicio.dals','w')
	archi.write('sig '+ clase +' extends java_lang_Object {}{}\n') 
	archi.write('abstract sig actionExec{}\n') 
	cade = 'one sig name_ac extends actionExec{}\n'
	prg=[]

	#aca3 definif dos funciones
	# setea_parametros_de_accion(d,a[0]), d es el pefil y a es el par (nombre_metodo, codigo) buscar en d ls parametros de a[0]
	#	para cada preguntar si para cada par de parametros tipo nombre_parametro, el tipo es 
	#       un  tipo no simple (diferente de int y bool), si es asi se debe insertar get_TIPO[v:TIPO, s: set TIPO ] 
	#       antes de la accion. para cada tipo
	#
	#guardar_en_set(a[0],return_int,d) esta funcion debe 
	# obtener el retorno k de la accion a[0] Y METER  set_k[return_k, set_TIPO] 

        for a in metodos:
	    ll=d[a[0]]
	    archi.write(cade.replace('name_ac',a[0])) 

	#aca5  va un if por cada tipo de retorno entrado en el programa. refactorizar 

	    if ll[0]=='I':
	           prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+'; '+ 'ac:='+a[0]+';validint:=true) ')
	    if ll[0]=='B':
                   prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+'; '+ 'ac:='+a[0]+';validbool:=true) ')
 	    if ll[0]=='V':
                   prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+';'+'ac:='+a[0]+')')
 	    if ll[0]=='Lista':
                   prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+';'+'ac:='+a[0]+guardar_en_set("set_Lista")+')')
 	    if ll[0]=='TS':
                   prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+';'+'ac:='+a[0]+guardar_en_set("set_TS")+')')	   	
 	    if ll[0]=='LNode':
                   prg.append('('+setea_parametros_de_accion(d,a[0],tipos_comp)+a[1]+';'+'ac:='+a[0]+guardar_en_set("set_LNode")+')')





	
	
	ini_sets= predicados_y_acciones_inicializadores_de_sets(tipos_comp)
	archi.write("//juan\n")
	archi.write(ini_sets+'\n')
	archi.write("//victoria\n")




	# aca1 - listo  
	# gen_codigo_inicializadores(tipos_comp) debe recorer tipos_comp y retornar una cadena 
	# del tipo ini_TIPO[set_TIPO] 




	p = '\nprogram={\n '+gen_codigo_inicializadores(tipos_comp,clase)+' ('
	for i in range(0,len(prg)):
	   if i==len(prg)-1:	
		    p = p + prg[i]+'\n)*}'	
	   else: 
		    p = p + prg[i]+'\n' +'+'+'\n'
	print '_______________________________'        
	print p
	print '_______________________________'        



	programa=programa.replace('__wap__',p)
	archi.write(programa)
	archi.write('\ncheck programa_wap\n')
	archi.close()



def predicados_y_acciones_inicializadores_de_sets(tipos_comp):
	#tipos_comp es una lista de los tipos no simples encontrados en el codigo fuente.
	#debemos recorrer esta lista greando un string con las acciones dyn para inicializar cada tipo.
	# tambien conviene crear las acciones de set y get elementos de los sets asociados a estos tipos
	res=''
	cade_ini= ' action ini_TIPO[set_TIPO: set TIPO]{\npre{TruePred[]} \n post{pos_ini_TIPO[set_TIPO\']} }\n'
	cade_ini= cade_ini+' pred pos_ini_TIPO[set_TIPO:set TIPO]{\n no set_TIPO\n }\n'

	cade_ini= cade_ini+' action get_TIPO[v:TIPO, set_TIPO: set TIPO ]{\n pre{TruePred[]}\npost{pos_get_TIPO[v,set_TIPO]}}\n'

	cade_ini= cade_ini+' pred pos_get_TIPO[v:TIPO,set_TIPO:set TIPO]{\nsome a:TIPO | a in set_TIPO && v==a }\n'
	cade_ini= cade_ini+' action guardar_TIPO[v:TIPO, set_TIPO: set TIPO ]{\n pre{TruePred []}\n post{pos_set_TIPO[v,set_TIPO,set_TIPO\']}\n}' 
	cade_ini= cade_ini+' pred pos_set_TIPO[v:TIPO, set_TIPO: set TIPO,set_TIPO\':set TIPO]{\nset_TIPO\'= set_TIPO+v}\n'
	for t in tipos_comp:	
		res=res+cade_ini.replace('TIPO',t)			
	return res	
		


def gen_codigo_inicializadores(tipos_comp,clase):
	res=''
	for t in tipos_comp:
		res=res+' ini_'+t+'[set_'+t+']; '
	if not res=='':
		res=res+' guardar_'+clase+'[thiz,set_'+clase+'];'
	return res





	#aca3 definif dos funciones
	# setea_parametros_de_metodo(d,a[0]), d es el pefil y a es el par (nombre_metodo, codigo) buscar en d ls parametros de a[0]
	#	para cada preguntar si para cada par de parametros tipo nombre_parametro, el tipo es 
	#       un  tipo no simple (diferente de int y bool), si es asi se debe insertar get_TIPO[v:TIPO, s: set TIPO ] 
	#       antes de la accion. para cada tipo
	#
	#guardar_en_set(a[0],return_int,d) esta funcion debe 
	# obtener el retorno k de la accion a[0] Y METER  set_k[return_k, set_TIPO] 


def setea_parametros_de_accion(perfiles, accion,tipos_comp):
	res=''	
        cade= 'get_TIPO[parametro,setipo ];'
	p= perfiles[accion]	
	#print '*****************'
	#print p	
	#print '*****************'		
	if len(p)>1:
  	   for i in xrange(1,len(p),2):

		tipo=p[i]
		if tipo in tipos_comp:
			parametro=p[i]
			newcade=cade.replace('TIPO',tipo)
			newcade=newcade.replace('parametro',parametro)
			newcade=newcade.replace('setipo','set_'+tipo)
			res=res+newcade


	return res

def guardar_en_set(set_retorno):
# habria que agregar una linea por tipo de retorno compuesto del programa - refatorizar
	if set_retorno=='set_Lista':
		res= '; guardar_Lista[return_Lista,set_Lista]'
	if set_retorno=='set_TS':
		res= '; guardar_TS[ return_TS,set_Lista]'
	if set_retorno=='set_LNode':
		res= '; guardar_LNode[ return_LNode,set_LNode]'

	return res	



# genera un string fact para input de listas
# valores es una lista de enteros
def gen_input_fact_Lista_old(valores):
	res='  fact{'
	res = res +'  equ[(QF.thiz_0).(QF.Lista_size_0),'+str(len(valores))+' ]  '
	cade='.(QF.LNode_next_0)'
	for i in xrange(0,len(valores)):
	 	res = res + ' and  equ[(QF.thiz_0).(QF.Lista_head_0).(QF.LNode_index_0),'+str(i)+'] ' 
		k=0
		for k in range(0,i):
			cade=cade+cade
	 	res = res + ' and  equ[(QF.thiz_0).(QF.Lista_head_0)'+cade+'.(QF.LNode_value_0),'+ str(valores[i])+'] ' 

	res=res+'} '
	return res


def gen_input_fact_TS(valores):
	res='  fact{'
	res = res +'  equ[(QF.thiz_0).(QF.TS_size_0),'+str(len(valores))+' ]  }'
	return res
'''
	cade='.(QF.LNode_next_0)'
	if len(valores)>0:
		res=res + ' and equ[(QF.thiz_0).(QF.Lista_head_0).(QF.LNode_value_0),'+str(valores[0])+' ]  '
		res=res + ' and equ[(QF.thiz_0).(QF.Lista_head_0).(QF.LNode_index_0),0]'
		for i in xrange(1,len(valores)):
				for k in range(1,i):
					cade=cade+cade
			 	res = res + ' and  equ[(QF.thiz_0).(QF.Lista_head_0)'+cade+'.(QF.LNode_value_0),'+ str(valores[i])+'] '
			 	res = res + ' and  equ[(QF.thiz_0).(QF.Lista_head_0)'+cade+'.(QF.LNode_index_0),'+ str(i)+'] '  

	res=res+'} '
'''
	








def gen_input_fact(i,lista): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	if (i<len(lista)):

		cade=lista[i]
		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+cade+"\/\*FIN_PRE\*\//g ' resultado.als")













#aca seguir
def leer_lista(i,lista_in):
	#abrir el archivo randoopStatesList y buscar la linea i
	lista=[]

	if i<len(lista_in):
		linea= lista_in[i]
		linea=linea.replace('\n','')
		linea=linea.strip()
		linea=linea[1:]
		linea=linea[:-1]
		lista=linea.split(',')
		lista2=[]
		for i in lista:
			if not i=='':
				lista2.append(int(i))
		return lista2 







#traer_pres_desde_archivo_c("/home/marcelo/salida_TS.txt")
