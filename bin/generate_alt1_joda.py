import ap2,os,sys,glob,ap1,time
from sets import Set






def gen_input_fact_i32(caso,i,lista,accion,loops,pin,result): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
		#scope_int=minBitwidthToRepresent(t)
		#check='check programa_wap for '+str(t)+" but "+str(n)+" JavaPrimitiveIntegerValue, "+str(scope_int)+" int" 
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				#cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])
				#	cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		print pares[' lista']
		print 'action to fix: '+accion+"("+cade+")"		 
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion



			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")

		
				predicado=predicado.split("\n")[0]



		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+pegar+"\/\*FIN_PRE\*\//g ' resultado.als")

		result[i]=out
	return [pares['size'],result]

def size_ent(i,lista): 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		return int(pares['size'])
	else:
	        return -1	

######################################################################################
def traer_pres_desde_archivo(archi_texto):
    f = open(archi_texto, "r")
    res=[] 	
    t = f.read()
    f.close()
    while True:
	    r=ap1.textoEnmedio(t, "<INICIO>", "<FINAL>")	
	    if (r==''):
		break
	    res.append(r) 
	    i=t.find("<FINAL>")	
	    t=t[i+7:]

    return res	
########################################################################################


def read_action(caso):
 casos_de_studio= os.listdir('../examples')
 if not (caso in casos_de_studio):
    print 'Error: No existe el caso de estudio.'	 
 else:
    parametros_del_prog_dyn= set([])
    #busca la lista de acciones dentro del directorio corespondiente al caso de estudio	
    
    lista_ac = glob.glob('../examples/'+caso+'/actions/*_act')
    
    #dic es un diccionario con toda la info necesaria de cada accion	
    dic={} 

    #one_sig_actions es una lista con todas las acciones que extiende de actionExec{}		
    one_sig_actions=[]

    #para cada accion se extraen sus datos	

    for accion in lista_ac:
	f = open(accion,'r')
	texto = f.read()
	f.close
	i=texto.find('act')+3
	s=texto[i:]
	j=s.find('[')

	#name_action nombre de la accion
	name_action=s[:j].strip()
	one_sig_actions.append("one sig "+name_action+" extends actionExec{}")


	name_action=name_action.strip()
	k=s.find(']')
	p=s[j+1:k]
	parametros=p.split(',')
	invo=name_action+'['

	#pin pout pinout son listas de los parametros de cada accion (entrada, salida y entrada-salida)
	pin=[]
	pout=[]
	pinout=[]
       
       	for e in parametros:
                
		n=e.find('*/')
		es=e[e.find('/*')+2:n].strip()
		t=e[n+2:].split(':')
		name_parametro=t[0].strip()
	         
		name_tipo=t[1].strip()
	        #print pin
		parametros_del_prog_dyn.add(name_parametro.strip()+':'+name_tipo.strip())
		if es=='in':
			pin.append([name_parametro.strip(),name_tipo.strip()])
		if es=='out':
			pout.append([name_parametro.strip(),name_tipo.strip()])
		if es=='inout':
			pinout.append([name_parametro.strip(),name_tipo.strip()])
		invo=invo+name_parametro+','
	
	invo=invo[:len(invo)-1]+']'
        	#parametros de la accion

	#invocacion de la accion, faltan los inicializadores adelante y tener en cuenta si hay sets  y los valids

	#cade_prog es un string donde se construye el call de la accion con sus respectivas inicializaciones 
	cade_prog=''
	
	

        	
	for e in pin:
		if e[1]=='Int':
			cade_prog=cade_prog+'gen_intA['+e[0]+'] ; '
		if e[1]=='boolean':
			cade_prog=cade_prog+'gen_bool['+e[0]+'] ; '
		if e[1]=='JavaPrimitiveIntegerValue':
                        
			cade_prog=cade_prog+'gen_intJ['+e[0]+'] ; '
	
        
        cade_prog=cade_prog+invo+'; ac:='+name_action
	valid=''
	pa_out=[]

	for e in pout:
		pa_out.append(e[0])
		if e[0]=='ret_val_int':
			cade_prog=cade_prog+' ; valid_intA:=true'
			valid="valid_intA'"
			if(len(pout)>1):
			    cade_prog='init_set[set_intA];'+cade_prog
			    parametros_del_prog_dyn.add('set_intA:set Int')
		if e[0]=='return_bool':
			cade_prog=cade_prog+' ; valid_bool:=true'
			valid="valid_bool'"
			if(len(pout)>1):
			    cade_prog='init_set[set_bool];'+cade_prog
			    parametros_del_prog_dyn.add('set_bool:set boolean')
		if e[0]=='return_intJ_1':
			cade_prog=cade_prog+' ; verify_null[return_intJ_1,valid_intJ]'  
			valid="valid_intJ'"
			if(len(pout)>1):
			    cade_prog='init_set[set_intJ];'+cade_prog
			    parametros_del_prog_dyn.add('set_intJ:set JavaPrimitiveIntegerValue')
		if e[0]=='return_intJ_2':
			cade_prog=cade_prog+' ; verify_null[return_intJ_2,valid_intJ]'  
			valid="valid_intJ'"
		if e[0]=='return_intJ_3':
			cade_prog=cade_prog+' ; verify_null[return_intJ_3,valid_intJ]'  
			valid="valid_intJ'"
		if e[0]=='return_intJ_4':
			cade_prog=cade_prog+' ; verify_null[return_intJ_4,valid_intJ]'  
			valid="valid_intJ'"
			
	cade_prog='('+cade_prog+')'

        
	#cadena de invocacion que va a ir en la *

	s= s[s.find('{')+1:]
	i=s.find('{')
	f=s.find('}')
	precondicion_accion= s[i+1:f].strip()
	s=s[f+1:]
	i=s.find('{')
	f=s.find('}')


	poscondicion_accion= s[i+1:f].strip()
	 

	
	#scope se agrega al final de cada accion con un comentario /*scope:n*/
	scope= s[s.find('/*')+8:s.find('*/')]
	name_postcondicion=poscondicion_accion[:poscondicion_accion.find('[')].strip()
	
	n= texto.find(name_postcondicion)

	#pred_postcondicion_programa es el predicado pos de la accion rota del programa dyn.
	pred_postcondicion_programa= 'pred pred_not'
	params=texto[n+len(name_postcondicion):].strip()
	
	params=params[:params.find(']')].strip()
	#print params
	tipos= params[1:].strip().split(',')
	#print tipos
        #print '-----------------------------' 

	tipos_ac_rota_formales=[]
        #print '-----------------------------'
        #print tipos

        for e in tipos:
		#print e
		tipos_ac_rota_formales.append(" ".join(e.split(':')[1].split()))


	
	#lista con los tipos de los parametros de la pos de la accion rota


	pl=[]
	pl1=[]
	for i in range(0,len(tipos_ac_rota_formales)):
		pl.append('p_'+str(i)+':'+tipos_ac_rota_formales[i])
		pl1.append('p_'+str(i))
	
	pos_not= pred_postcondicion_programa+"["+",".join(pl)
	cuerpo="["+",".join(pl1)+"]"
	cuerpo=name_postcondicion+cuerpo
        
	if len(pout)==0:#si tiene retorno
		pos_not=pos_not+']{ not('+cuerpo+')}'
	if len(pout)==1:#si tiene retorno
		pos_not=pos_not+',b:boolean]{ not('+cuerpo+' and b=true)}'
	
	if len(pout)==2:#si tiene 2 retornos
		#ver para maps u otra estructura que retorna objetos compuestos

		npos=poscondicion_accion.replace(pout[0][0]+"'",'a')
		npos=npos.replace(pout[1][0]+"'",'b')

		#aca buscar en npos los parametros que correspondan, para a y b estan ok, ver si cuerpo tiene 
		cuerpo=cuerpo.replace('p_0','a')
		cuerpo=cuerpo.replace('p_1,','v,')
		cuerpo=cuerpo.replace('p_1],','v')
		npos=cuerpo
		same='(some a,v:'+pout[0][1]+'| a in set_intJ and v in set_intJ and '+npos+')'

		pos_not=pos_not+',b:boolean,set_intJ:set univ]{ not('+same+' and b=true)}'
		
        if len(pout)==3:#si tiene 3 retornos
		#ver para maps u otra estructura que retorna objetos compuestos
                
		npos=poscondicion_accion.replace(pout[0][0]+"'",'a')
		npos=npos.replace(pout[1][0]+"'",'v')
		npos=npos.replace(pout[2][0]+"'",'c')
		#aca buscar en npos los parametros que correspondan, para a y b estan ok, ver si cuerpo tiene 
		cuerpo=cuerpo.replace('p_0','a')
		cuerpo=cuerpo.replace('p_1,','v,')
		cuerpo=cuerpo.replace('p_1],','v')
                cuerpo=cuerpo.replace('p_2','c')
		npos=cuerpo
		same='(some a,v,c:'+pout[0][1]+'| a in set_intJ and v in set_intJ and c in set_intJ and '+npos+')'

		pos_not=pos_not+',b:boolean,set_intJ:set univ]{ not('+same+' and b=true)}'
	if len(pout)==4:#si tiene 4 retornos
		#ver para maps u otra estructura que retorna objetos compuestos
		npos=poscondicion_accion.replace(pout[0][0]+"'",'a')
		npos=npos.replace(pout[1][0]+"'",'v')
		npos=npos.replace(pout[2][0]+"'",'c')
                npos=npos.replace(pout[3][0]+"'",'d')

	#aca buscar en npos los parametros que correspondan, para a y b estan ok, ver si cuerpo tiene 
		cuerpo=cuerpo.replace('p_0','a')
		cuerpo=cuerpo.replace('p_1,','v,')
		cuerpo=cuerpo.replace('p_1],','v')
                cuerpo=cuerpo.replace('p_2','c')
                cuerpo=cuerpo.replace('p_3','d')
		npos=cuerpo
		same='(some a,v,c,d:'+pout[0][1]+'| d in set_intJ and a in set_intJ and v in set_intJ and c in set_intJ and '+npos+')'

		pos_not=pos_not+',b:boolean,set_intJ:set univ]{ not('+same+' and b=true)}'
	
		
        
	p=poscondicion_accion[poscondicion_accion.find('['):poscondicion_accion.find(']')].strip()

	lista=p.split(',')
	if valid=='':
		invo_pos_not='pred_not'+p+']'
	else:
		invo_pos_not='pred_not'+p+','+valid+']'
        #print pout
	#sys.exit(0)
        # print '-------------------------------------------------------'
	if len(pout)>=2:#si tiene 2 o mas retornos
                
		invo_pos_not='pred_not'+p+','+valid+',set_intJ]'
	 
        


	#invo_pos_not es la poscondicion actual del programa roto
	dic[accion]=[invo_pos_not,pos_not,name_action,cade_prog,poscondicion_accion,precondicion_accion,pin,scope,pa_out]

            #pametros del programa dynalloy hace un set con todos los parametros que va a tener el programa	
    parametros_del_prog_dyn.add('valid_intA:boolean')
    parametros_del_prog_dyn.add('valid_intJ:boolean')
    parametros_del_prog_dyn.add('valid_bool:boolean')
    parametros_del_prog_dyn.add('ac:actionExec')

    


    dic['parametros_dyn']=parametros_del_prog_dyn
    dic['one_sig_actions']=one_sig_actions

	
    return dic
########################################################################################




def minBitwidthToRepresent(size):
        k = 1;
	while True:
		if (size>pow(2,k)/2-1):
			k=k+1;
		else:
		  	return k;






def traer_pres_desde_archivo(archi_texto):
    f = open(archi_texto, "r")
    res=[] 	
    t = f.read()
    f.close()
    while True:
	    r=ap1.textoEnmedio(t, "<INICIO>", "<FINAL>")	
	    if (r==''):
		break
	    res.append(r) 
	    i=t.find("<FINAL>")	
	    t=t[i+7:]

    return res	



def gen_input_fact_i32(caso,i,lista,accion,loops,pin,result): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
		#scope_int=minBitwidthToRepresent(t)
		#check='check programa_wap for '+str(t)+" but "+str(n)+" JavaPrimitiveIntegerValue, "+str(scope_int)+" int" 
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				#cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])
				#	cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		print pares[' lista']
		print 'action to fix: '+accion+"("+cade+")"		 
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion



			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")

		
				predicado=predicado.split("\n")[0]



		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+pegar+"\/\*FIN_PRE\*\//g ' resultado.als")

		result[i]=out
	return [pares['size'],result]

##################################################################################################
def nume(s):
   m=s.split('.')
   if len(m)>1:
        t=m[1]  	
        return m[0]+'.'+t[0:3]
   else:
	return m[0]	
##################################################################################################
def fix_alt1(caso,accion,pin,tiempo_to,input_file):
   result={} 	
   

   entradas=traer_pres_desde_archivo('../examples/'+caso+'/'+input_file)	
   
   cont=0
   size_wac_max=30  
   sum_long_wa=0	
   cont_wa=0
   tiempo_total=0
   entradas_procesadas=0	
   prom_tam_listas=0
   suma_tam_listas=0
   ttotal=0
   ttotal_sin_to=0	
   emin=10000
   temin=0
   emax=0 	
   temax=0
   to=0
   for i in range(0, len(entradas)):
	
	print '<control '+str(i)+'>'
        primer_wac=False
        scope='7'
        if primer_wac:
		break   
	print 'searching workarounds...\n'
	tiempo_inicio_wa=time.time()
        print 'kkk' 
	timeout=300
        cambio_i=False
        tama=size_ent(i,entradas)   
	for unroll in range(1,size_wac_max+1):
      
                    if primer_wac:
		        t2=time.time()-tiempo_inicio_wa	
			ttotal=ttotal+t2
		        ttotal_sin_to=ttotal_sin_to+t2
		        if emin >= tama: 
                           
                          if (emin==tama  and temin<t2) or (emin > tama):
				                       temin=t2 
                          emin=tama 
                        if emax <= tama: 
                          if (emax==tama and temax<t2) or (emax < tama):
		              			       temax=t2 
                          emax=tama
		        break	
   		    if ((time.time()-tiempo_inicio_wa)>timeout):
			print "Timeout "+str(timeout)
                        linea="-------------------------------------------------------"
		        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		        os.system(rr)
			t2=time.time()-tiempo_inicio_wa	
			tiempo_total=tiempo_total+t2
			ttotal=ttotal+t2
                        to=to+1
			break	                    
		    
   	    	    				
     	            ap1.run_modelo_dynalloy('temporalnew.dals','resultado.als',str(unroll))
		    
                    t2=time.time()-tiempo_inicio_wa	



		    ap1.rempla('resultado.als','check programa_wap',' ') 

	
              	    os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> resultado.als')
		    				
                    

		    #la funcion siguiente es la que actualuiza las pre de resultado.als	


		    #pred_aux son predicados auxiliares dependientes del tamanio de la estructura	

		    print 'size: '+str(tama)	
		    linea='size: '+str(tama)
  	            rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		    os.system(rr)		     
		    res=gen_input_fact_i32(caso,i,entradas,accion,unroll,pin,result)
		    size_lista=res[0]
		    p=result[i]	
		    p.append('size: '+str(tama))


		    result=res[1]
		    if not cambio_i:   
		    	    suma_tam_listas= int(size_lista)+suma_tam_listas
			    
			    cambio_i=True 	


		 	
		   
                 
			
                    ap1.run_modelo_alloy('resultado.als',i,unroll,accion,caso,1,tiempo_to)

	
		    os.system('cp resultado.als ../examples/'+caso+'/results/alt1/wa_'+caso+'_'+accion+'_in_'+str(i)+'unroll_'+str(unroll)+'.als')


		    wac=[]
		    cc=1	

		    if ap1.UNSAT('temp')==1:
		      print 'there is no workarounds size:'+ str(unroll)
  		      linea='there is no workarounds size:'+ str(unroll)
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)



		      p.append('there is no workarounds size:'+ str(unroll))		
	            if ap1.UNSAT('temp')==2 and (ap1.time_time(tiempo_to)<=t2):
		      print 'timeout for '+ str(unroll)+' unrolls.'
  		      linea='timeout for '+ str(unroll)+' unrolls.'
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)
                      linea="-------------------------------------------------------"
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)


		      p.append('timeout para <control '+str(i)+'>')
		      t2=time.time()-tiempo_inicio_wa	
		      tiempo_total=tiempo_total+t2	
		      		
		    else:
		      if ap1.UNSAT('temp')==0:
	       	      #si entra por el else encontro un wac	
			wac_Ok= 0	
	                if (primer_wac==False): 
				primer_wac=True
				entradas_procesadas=entradas_procesadas+1
				t2=time.time()-tiempo_inicio_wa	
				tiempo_total=tiempo_total+t2
				
				
 				print 'first wac found in: '+ str(t2)+' seconds.'

				linea='first wac found in: '+ str(t2)+' seconds.'
				rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
				os.system(rr)

   			        p.append('first wac found in: '+ str(t2)+' seconds.')
				primer_wac=True

	  	  	while cc<=size_wac_max and ap1.UNSAT('temp')==0:
	
		    			if ((time.time()-tiempo_inicio_wa)>timeout):
							break
					
					#SI QF es true removeQuantifier debe ser true
					qf= True
					#usar perfiles
					wac= ap1.extraccion__wac('resultado.alsuva',qf)
		    		        ap1.expor('../examples/'+caso+'/results/alt1/alt1_wa_'+accion+'_unrool_'+str(unroll)+'_control',i)
					print 'wac\n'
					print wac
					p.append('wac: '+str(wac))
					cont_wa=cont_wa+1
					#suma_tam_listas= int(size_lista)+suma_tam_listas
					sum_long_wa=sum_long_wa+unroll
					
					if primer_wac:
						break
			
					#sale al encontrar el primer wac
                   			print "...adding  not wac to resultado.dals... "

					accion_qf=''
					if qf:
						for e in wac:
							accion_qf='and (not(QF.'+e+'))\n'						
							pre_randoop.update_als(sys.argv[1]+'_ensures_'+sys.argv[2]+'[',accion_qf)
	


					else:
						cade= ap1.generar_cade_para_modelo_als(wac)
 					        ap1.buscar__insertar(cade,'resultado.als')



		    			ap1.run_modelo_alloy('resultado.als',i,unroll,sys.argv[2],1)
		    			os.system('cp resultado.als ../examples/'+caso+'/results/alt1/wa_'+caso+'_'+sys.argv[2]+'_in_'+str(i)+'unroll_'+str(unroll)+'.als')
					cc=cc+1
					if cc > size_wac_max:
						print 'Maximum limit is reached.'
						p.append('Maximum limit is reached.')
	
		                	if cc <=size_wac_max:
						print 'Not found more wacs for this size.'
						p.append('Not found more wacs for this size.')

		    # delete temporal files
                    os.system('rm temp')
	print 'updating...'
	result[i]=p

   
   cant_estados=len(entradas)
   final=''	


   print '---------------------------------------------------'	
   resultado = 'Action '+ accion
   resultado = resultado +' | Number of inputs processed: '+str(cant_estados)
   print resultado
   resultadof = resultado + '|'

   if (cant_estados>0):	
	   resultadof = resultadof + "Avg. input size: " +nume(str(float(suma_tam_listas)/float(cant_estados)))+ '|'
	   print  "Avg. input size: " +nume(str(float(suma_tam_listas)/float(cant_estados)))


   print 'Number of workarrounds found: '+str(cont_wa)
   resultadof=resultadof+'Number of workarrounds found: '+str(cont_wa)+ '|'



   print 'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(to)
   resultadof=resultadof+'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(to)+ '|'

   if (cont_wa>0):
   	prome=ttotal_sin_to/float(cont_wa)
	resultadof=resultadof+'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.'

   if (cont_wa>0):
   	prome=ttotal/float(cont_wa)
	resultadof=resultadof+'Avg. time to find a workaround: '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround: '+nume(str(prome))+' seconds.'



   resultadof=resultadof+'Total running time: '+nume(str(float(ttotal)))+' seconds.|'
   print 'Total running time: '+nume(str(float(ttotal)))+' seconds.'


   if not emin==10000:
   	resultadof=resultadof+'Smallest input size: '+str(emin)+' elements.|'
   	print 'Smallest input size: '+str(emin)+' elements.'
	resultadof=resultadof+'Maximum time to find a workaround for the smallest input: '+nume(str(temin))+'|'
   	print 'Maximum time to find a workaround for the smallest input: '+nume(str(temin))
	        

   if not emax==-1:
        resultadof=resultadof+'Largest input size: '+str(emax)+' elements.'+'|'
        print 'Largest input size: '+str(emax)+' elements.'
        resultadof=resultadof+'Maximum time to find a workaround for the largest input: '+nume(str(temax))+'|'
        print 'Maximum time to find a workaround for the largest input: '+nume(str(temax))
		
   if (cont_wa>0):
   	prome=nume(str(float(sum_long_wa)/float(cont_wa)))
	resultadof=resultadof+'Avg. size of workarounds: '+nume(str(prome))+' seconds.|'
  	print 'Avg. size of workarounds: '+nume(str(prome))+' actions.'
   print '---------------------------------------------------'
   result[-1]=resultadof


   return result







def fix_alt1_jodatime(caso,accion,pin,tiempo_to,input_file):
   result={} 	
   
   entradas=[['h:2?m:3?s:34?mls:32'],['h:4?m:3&s:34&mls:32']]


   cont=0
   size_wac_max=30  
   sum_long_wa=0	
   cont_wa=0
   tiempo_total=0
   entradas_procesadas=0	
   prom_tam_listas=0
   suma_tam_listas=0
   ttotal=0
   ttotal_sin_to=0	
   emin=10000
   temin=0
   emax=0 	
   temax=0
   to=0
    
   for i in range(0, len(entradas)):
	print '<control '+str(i)+'>'
        primer_wac=False
        scope='7'
        if primer_wac:
		break   
	print 'searching workarounds..joda.\n'
	tiempo_inicio_wa=time.time()

	timeout=300
        cambio_i=False
        tama=4   
            
	for unroll in range(1,size_wac_max+1):
      
                    if primer_wac:
		        t2=time.time()-tiempo_inicio_wa	
			ttotal=ttotal+t2
		        ttotal_sin_to=ttotal_sin_to+t2
		        
		        break	
   		    if ((time.time()-tiempo_inicio_wa)>timeout):
			print "Timeout "+str(timeout)
                        linea="-------------------------------------------------------"
		        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		        os.system(rr)
			t2=time.time()-tiempo_inicio_wa	
			tiempo_total=tiempo_total+t2
			ttotal=ttotal+t2
                        to=to+1
			break	                    
		    
		    	
	            ap1.run_modelo_dynalloy('temporalnew.dals','resultado.als',str(unroll))
                    	
                    
                    t2=time.time()-tiempo_inicio_wa	



		    ap1.rempla('resultado.als','check programa_wap',' ') 

		    os.system('echo "check programa_wap" >> resultado.als') 
              	    os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> resultado.als')
		    
		    ap2.gen_fact_qf(unroll,accion)
        	    
                    sys.exit(0)

		    #la funcion siguiente es la que actualuiza las pre de resultado.als	


		    #pred_aux son predicados auxiliares dependientes del tamanio de la estructura	
                     
		   
		    #insertar la pre-condicion

  		     #aca
		    #res=gen_input_fact_i32_jt(caso,i,entradas,accion,unroll,pin,result)

		    
		   

		   
                 

                    ap1.run_modelo_alloy('resultado.als',i,unroll,accion,caso,1,tiempo_to)
		     	
	   	    os.system('cp resultado.als ../examples/'+caso+'/results/alt1/wa_'+caso+'_'+accion+'_in_'+str(i)+'unroll_'+str(unroll)+'.als')

		    #sys.exit(0) 	
		    wac=[]
		    cc=1	

		    if ap1.UNSAT('temp')==1:
		      print 'there is no workarounds size:'+ str(unroll)
  		      linea='there is no workarounds size:'+ str(unroll)
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)
		      p.append('there is no workarounds size:'+ str(unroll))		
  
	            if ap1.UNSAT('temp')==2 and (ap1.time_time(tiempo_to)<=t2):
		      print 'timeout for '+ str(unroll)+' unrolls.'
  		      linea='timeout for '+ str(unroll)+' unrolls.'
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)
                      linea="-------------------------------------------------------"
		      rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      os.system(rr)


		      p.append('timeout para <control '+str(i)+'>')
		      t2=time.time()-tiempo_inicio_wa	
		      tiempo_total=tiempo_total+t2	
		      		
		    else:
		      if ap1.UNSAT('temp')==0:
	       	      #si entra por el else encontro un wac	
			wac_Ok= 0	
	                if (primer_wac==False): 
				primer_wac=True
				entradas_procesadas=entradas_procesadas+1
				t2=time.time()-tiempo_inicio_wa	
				tiempo_total=tiempo_total+t2
				
				
 				print 'first wac found in: '+ str(t2)+' seconds.'

				linea='first wac found in: '+ str(t2)+' seconds.'
				rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
				os.system(rr)
				
   			        p.append('first wac found in: '+ str(t2)+' seconds.')
				primer_wac=True

	  	  	while cc<=size_wac_max and ap1.UNSAT('temp')==0:
	
		    			if ((time.time()-tiempo_inicio_wa)>timeout):
							break
					
					#SI QF es true removeQuantifier debe ser true
					qf= True
					#usar perfiles
					wac= ap1.extraccion__wac('resultado.alsuva',qf)
		    		        ap1.expor('../examples/'+caso+'/results/alt1/alt1_wa_'+accion+'_unrool_'+str(unroll)+'_control',i)
					print 'wac\n'
					print wac
					p.append('wac: '+str(wac))
					cont_wa=cont_wa+1
					#suma_tam_listas= int(size_lista)+suma_tam_listas
					sum_long_wa=sum_long_wa+unroll
					
					if primer_wac:
						break
			
					#sale al encontrar el primer wac
                   			print "...adding  not wac to resultado.dals... "

					accion_qf=''
					if qf:
						for e in wac:
							accion_qf='and (not(QF.'+e+'))\n'						
							pre_randoop.update_als(sys.argv[1]+'_ensures_'+sys.argv[2]+'[',accion_qf)
	


					else:
						cade= ap1.generar_cade_para_modelo_als(wac)
 					        ap1.buscar__insertar(cade,'resultado.als')



		    			ap1.run_modelo_alloy('resultado.als',i,unroll,sys.argv[2],1)
		    			os.system('cp resultado.als ../examples/'+caso+'/results/alt1/wa_'+caso+'_'+sys.argv[2]+'_in_'+str(i)+'unroll_'+str(unroll)+'.als')
					cc=cc+1
					if cc > size_wac_max:
						print 'Maximum limit is reached.'
						p.append('Maximum limit is reached.')
	
		                	if cc <=size_wac_max:
						print 'Not found more wacs for this size.'
						p.append('Not found more wacs for this size.')

		    # delete temporal files
                    os.system('rm temp')
	print 'updating...'
	result[i]=p

   
   cant_estados=len(entradas)
   final=''	

   
   print '---------------------------------------------------'	
   resultado = 'Action '+ accion
   resultado = resultado +' | Number of inputs processed: '+str(cant_estados)
   print resultado
   resultadof = resultado + '|'

   if (cant_estados>0):	
	resultadof = resultadof + "Avg. input size: " +nume(str(float(suma_tam_listas)/float(cant_estados)))+ '|'
	print  "Avg. input size: " +nume(str(float(suma_tam_listas)/float(cant_estados)))


   print 'Number of workarrounds found: '+str(cont_wa)
   resultadof=resultadof+'Number of workarrounds found: '+str(cont_wa)+ '|'



   print 'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(to)
   resultadof=resultadof+'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(to)+ '|'

   if (cont_wa>0):
   	prome=ttotal_sin_to/float(cont_wa)
	resultadof=resultadof+'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.'

   if (cont_wa>0):
   	prome=ttotal/float(cont_wa)
	resultadof=resultadof+'Avg. time to find a workaround: '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround: '+nume(str(prome))+' seconds.'



   resultadof=resultadof+'Total running time: '+nume(str(float(ttotal)))+' seconds.|'
   print 'Total running time: '+nume(str(float(ttotal)))+' seconds.'


   if not emin==10000:
   	resultadof=resultadof+'Smallest input size: '+str(emin)+' elements.|'
   	print 'Smallest input size: '+str(emin)+' elements.'
	resultadof=resultadof+'Maximum time to find a workaround for the smallest input: '+nume(str(temin))+'|'
   	print 'Maximum time to find a workaround for the smallest input: '+nume(str(temin))
	        

   if not emax==-1:
        resultadof=resultadof+'Largest input size: '+str(emax)+' elements.'+'|'
        print 'Largest input size: '+str(emax)+' elements.'
        resultadof=resultadof+'Maximum time to find a workaround for the largest input: '+nume(str(temax))+'|'
        print 'Maximum time to find a workaround for the largest input: '+nume(str(temax))
		
   if (cont_wa>0):
   	prome=nume(str(float(sum_long_wa)/float(cont_wa)))
	resultadof=resultadof+'Avg. size of workarounds: '+nume(str(prome))+' seconds.|'
  	print 'Avg. size of workarounds: '+nume(str(prome))+' actions.'
   print '---------------------------------------------------'
   result[-1]=resultadof


   return result


##################################################################################################################
def gen_input_fact_i32_jt(caso,i,lista,accion,loops,pin,result): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	out=[]
        
	#aca
	if (i<len(lista)):
		cade=lista[i]
		
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
		#scope_int=minBitwidthToRepresent(t)
		#check='check programa_wap for '+str(t)+" but "+str(n)+" JavaPrimitiveIntegerValue, "+str(scope_int)+" int" 
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				#cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])
				#	cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		#print pares[' lista']
		print 'action to fix: '+accion+"("+cade+")"		 
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion



			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")

		
				predicado=predicado.split("\n")[0]



		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+pegar+"\/\*FIN_PRE\*\//g ' resultado.als")

		result[i]=out
	return [pares['size'],result]


##################################################################################################################


def size_ent(i,lista): 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		return int(pares['size'])
	else:
	        return -1
######################################################3
def acciones_con_parametro_k(accion):
    
    if(accion.find('get')>0):
	return True
    else:
	return False

######################################################3
def fix_alt1_jodatime2(caso,accion,pin,tiempo_to,input_file):
   #buscar en el archivo de las entradas y agregarlos en entradas_wag
   entradas=ap2.read_file_input_joda("entrada_wag_finder")
   
   ttotal=0
   ttotal_sin_to=0
   total_reparaciones=0
   total_estados=0
   cant_to=0

   size_wac_max=3 
   for i in range(0, len(entradas)-1):
	primer_wac=False
	print 'searching workarounds..joda.\n'
        salir=False
        total_estados=total_estados+1
	for unroll in range(1,size_wac_max):
		    if salir:
		         break
		    	
	      	    ap1.run_modelo_dynalloy('temporalnew.dals','resultado.als',str(unroll))
		    #agrega los enteros dependiendo de la cantidad de loops unroll
		    os.system('echo "check programa_wap for 0 but "'+ str(unroll*23) +' JavaPrimitiveIntegerValue  >> resultado.als')


	    
              	    os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> resultado.als')
		    initial_state=entradas[i].strip('\n')
		    initial_state=initial_state.replace('/*INICIO*/','')
		    initial_state=initial_state.replace('/*FIN*/','')


		    #parche para no incluir el QF.k_0 en las acciones que no tiene este parametro, ejemplo los get
	            if (not acciones_con_parametro_k(accion)):	
                    	initial_state=initial_state.replace('QF.k_0','QF.'+accion+"_k_0")
		    else:
			ind1=initial_state.find("and eq32[QF.k_0")
			initial_state=initial_state[:ind1]+"}"
			






                    ap2.gen_fact_qf(unroll,accion)
		    os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+initial_state+"\/\*FIN_PRE\*\//g ' resultado.als")
		    tinicio= time.time()
                    ap1.run_modelo_alloy('resultado.als',i,unroll,accion,caso,1,tiempo_to)
                    tfin= time.time()
		    os.system('cp resultado.als ../examples/'+caso+'/results/alt1/wa_'+caso+'_'+accion+'_in_'+str(i)+'unroll_'+str(unroll)+'.als')
		    

		    tanalisis= tfin-tinicio
 		    
                    ttotal=ttotal+tanalisis

   		    if ap1.UNSAT('temp')==1:
                      		ttotal_sin_to=ttotal_sin_to+tanalisis
  		      		linea='State number: '+str(i)+' there is no workarounds for unroll:'+ str(unroll)
		      		rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      		os.system(rr)
				print linea
				break

	            if ap1.UNSAT('temp')==2:
		      		linea='State number: '+str(i)+' TIMEOUT for '+ str(unroll)+' unrolls.'
				print linea
		      		rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		      		os.system(rr)
  		    	      	cant_to=cant_to+1
		      		
		    
		    if ap1.UNSAT('temp')==0:
		                total_reparaciones=total_reparaciones+1
				ttotal_sin_to=ttotal_sin_to+tanalisis
				linea='State number: '+str(i)+' first wac found in: '+ str(tanalisis)+' seconds.'
		      		rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
				print linea
		      		os.system(rr)
                                salir=True   
				break

   
   print '---------------------------------------------------'	
   resultado = 'Action '+ accion
   resultado = resultado +' | Number of inputs processed: '+str(total_estados)
   print resultado
   resultadof = resultado + '|'

  
   print 'Number of workarrounds found: '+str(total_reparaciones)
   resultadof=resultadof+'Number of workarrounds found: '+str(total_reparaciones)+ '|'



   print 'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(cant_to)
   resultadof=resultadof+'Number of failures (exceeding a '+tiempo_to+' timeout for trace): '+str(cant_to)+ '|'

   if (total_reparaciones>0):
   	prome=ttotal_sin_to/float(total_reparaciones)
	resultadof=resultadof+'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.'

   if (total_reparaciones>0):
   	prome=ttotal/float(total_reparaciones)
	resultadof=resultadof+'Avg. time to find a workaround: '+nume(str(prome))+' seconds.|'
  	print 'Avg. time to find a workaround: '+nume(str(prome))+' seconds.'
   resultadof=resultadof+'Total running time: '+nume(str(float(ttotal)))+' seconds.|'
   print 'Total running time: '+nume(str(float(ttotal)))+' seconds.'

   print '---------------------------------------------------'
   
   rr="echo '"+resultadof+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
   os.system(rr)












#############

