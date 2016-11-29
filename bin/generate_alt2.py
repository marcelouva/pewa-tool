import os,sys,glob,ap1,time
from sets import Set


def process(s):
	r=[]
	for e in s:
	   e="QF."+e
	   if e[len(e)-1]=="'":
		e=e[:len(e)-1]
		e=e+'_1'
	   else:
		e=e+'_0'
	   r.append(e) 	
	return r
	

########################################################################################
def generate_fact_alt_2(a):
	res=' fact{ '
	f= open(a,'r')
	texto=f.read()
	t=texto	
	f.close()

	i=t.find('act')
	parametros_act = t[i:]
	parametros_act = parametros_act[parametros_act.find('[')+1:parametros_act.find(']')].strip().split(',')


	pin=[]
	pp=[]
	pinout=[]
	pout=[]

	for p in parametros_act:
		n=p[p.find('*/')+2:].split(':')[0].strip()
		m=p[p.find('*/')+2:].split(':')[1].strip()
                if p.find('/*in*/')>=0:
			p=p[p.find('/*in*/')+6:]
			pin.append(p.split(':')[1])
			pp.append(n+'_0:'+m+',')
	        if p.find('/*out*/')>=0:
			p=p[p.find('/*out*/')+6:]
			pout.append(p.split(':')[1])
			pp.append(n+'_1:'+m+',')
	        if p.find('/*inout*/')>=0:
			p=p[p.find('/*inout*/')+6:]
			pinout.append(p.split(':')[1])
			pp.append(n+'_0:'+m+',')
			pp.append(n+'_1:'+m+',')


	cadeQF="".join(pp)
	cadeQF=" sed -i 's/\/\*INICIO.*FIN\*\//\/\*INICIO\*\/"+cadeQF+"\/\*FIN\*\//g ' "

	s=t[i:]
	s=s[s.find('pre'):]
	pre=s[s.find('{')+1:s.find('}')].strip()
	#pre_name es el nombre del predicado pre
	pre_name=pre[:pre.find('[')].strip()
	
	pre_params=pre[pre.find('[')+1:pre.find(']')].strip().split(',')
	if not pre_params==['']:
		pre_params='['+','.join(process(pre_params))+']'
	else:
		pre_params='[]'




	res=res+pre_name+pre_params+'\n'
	s =s[s.find('post'):]
	z=s.find('}')	
	pos=s[s.find('{')+1:z].strip()

	pos_name=pos[:pos.find('[')].strip()
	pos_params=pos[pos.find('[')+1:pos.find(']')].strip().split(',')

	pos_params='['+','.join(process(pos_params))+']'

	res=res+pos_name+pos_params+'\n}\n'
	ini=t.find('/*scope:')+8
	k=t[ini:]
	f=k.find('*/')
	scope=k[:f]
	#res contine el fact a insertar#
	new=[texto[:i]+res,scope,pin,cadeQF]

	return new

#######################################################################################

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

#######################################################################################
def input(cade):
	data=cade.split('?')
	pares={}
	for e in data:
	   s=e.split(':')
	   pares[s[0].strip()]=s[1].strip()			
	return pares

#######################################################################################
#prefijo es el prefijo del archivo del modelo,accion es la accion a reparar y scope sirve para encontrar el  modelo pre-geneado
def gen_resultado_als(prefijo,accion,scope,modelo_accion,fact_in,cadeQF):

   sc=int(scope)+2	
   if (sc<=100):
	if(sc<=2):
		scope='3'

	os.system(cadeQF+" "+prefijo+str(scope)+'.als')
	f = open(prefijo+str(scope)+'.als', "r")
	modelo=f.read()
	f.close()
	f = open('resultado.als','w')
	f.write(modelo)
	f.write(modelo_accion)
	f.write(fact_in)
	f.close()
   else:
	print "Error: no pre-generated models for this scope."	  	

####################################################################################33
def nume(s):
   m=s.split('.')
   if not len(m)==2:	
     return ''
   else: 	
     t=m[1]  	
     return m[0]+'.'+t[0:3]


#######################################################################################
def fix_a2(caso,accion,sc,pin,accion_name,cadeQF,tiempo_to,input_file):
   cant_estados=0
   cant_wa=0
   ttotal=0
   ttotal_sin_to=0
   tpromedio=0	 
   suma_tam_lista=0		
   to=0
   i=0

   entradas=traer_pres_desde_archivo('../examples/'+caso+'/'+input_file)	
   modelo_alloy_accion= accion
   emin=10000
   emax=-1 	
   temin=0
   temax=0	
   for entrada in entradas:
	print 'control<'+str(i)+'>' 
	nd=input(entrada)
	suma_tam_lista=suma_tam_lista+int(nd['size'])
	sn=str(int(nd['size'])+int(sc))
	p=0
	f=0
	res=[]
	cade=''
	parametros_de_acciones=''
	
	if len(pin)>0:
		for e in pin:
		     if (e=='JavaPrimitiveIntegerValue' and p==0 and cadeQF.find('intJ_1_0')>0):	
				res.append( "QF.intJ_1_0="+nd['pi32_a'])
				p=1
		     else:	
			     if(e=='JavaPrimitiveIntegerValue' and p==1 and cadeQF.find('intJ_2_0')>0):	
					res.append( "QF.intJ_2_0="+nd['pi32_a'])

		     if (e[1]=='Int'and f==0 and cadeQF.find('intA_1_0')>0):	
				res.append("equ[QF.intA_1_0,"+nd['indice_a']+"]")
				cade=cade+" "+e+"="+nd['indice_a']
				f=1
		     else:
	  	     	     if (e=='Int'and f==1 and cadeQF.find('intA_2_0')>0):	
				res.append("equ[QF.intA_2_0,"+nd['indice_b']+"]")
				cade=cade+" "+e+"="+nd['indice_b']
		parametros_de_acciones=" fact { "+(" and ").join(res)+"} "

		fact_in=nd['estado']+parametros_de_acciones

	else:
		fact_in=nd['estado']	


	
	
        linea='Control<'+str(i)+'>' 
        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
	os.system(rr)

	
	print 'size: '+nd['size']
        linea='size: '+nd['size'] 
        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
	os.system(rr)

	print 'input : '+ nd['lista']
        linea=nd['lista']
        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
	os.system(rr)


	print 'action to fix: '+accion_name+"("+cade+")"
        linea='action to fix: '+accion_name+"("+cade+")"
        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
        os.system(rr)
	
	# lee el prefijo del archivo de configuracion config.ini
	cadena = ap1.read_config_case("../config.ini","case_"+caso)['prefix']


	#ajusta la cantidad de enteros java a exactamente lo que necesita
        # para ello reemplaza la clausula exactly del modelo als por la que viene del estado inicial de randoop


	#aca si size con cantidad_enteros es diferente habria que agregar los v10 , v11
	#print '-----------------------'	
	#print nd['size']
	#print nd['cantidad_enteros']
	#print '-----------------------'


	os.system("sed -i 's/exactly[[:space:]][0-9]*[[:space:]]*JavaPrimitiveIntegerValue/exactly "+str(nd['cantidad_enteros'])+"  JavaPrimitiveIntegerValue/g' "+" ../examples/"+caso+"/models/"+cadena+str(sn)+".als")
	



	gen_resultado_als('../examples/'+caso+'/models/'+cadena,caso,sn,modelo_alloy_accion,fact_in,cadeQF)








	tiempo_inicio_wa=time.time()
	######################### call alloy analyzer   ############################### 

  	ap1.run_modelo_alloy_pewa('resultado.als',i,0,accion_name,caso,2,tiempo_to)


	###############################################################################
        t2=time.time()-tiempo_inicio_wa












	ttotal=ttotal+t2
	
	tiempo_o = ap1.read_config_case("../config.ini","options")['timeout']


	cant_estados=cant_estados+1
        
        #

        if ap1.UNSAT('temp')==2 and (ap1.time_time(tiempo_o)<=t2):  
		to=to+1
		print 'timeout.'
                rr="echo 'timeout'  >> ../examples/"+caso+"/results/alt2/alt2_output"
		os.system(rr)
		linea="-------------------------------------------------------"
	        rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
	        os.system(rr)

	
        if ap1.UNSAT('temp')==1:  
		print 'Workaround not found.'
		linea='Workaround not found. '
		rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
		os.system(rr)

        if ap1.UNSAT('temp')==0:  
	        ap1.expor('../examples/'+caso+'/results/alt2/wa_'+caso+'_'+accion_name+'_',i)
		os.system('cp resultado.als ../examples/'+caso+'/results/alt2/wa_'+caso+'_'+accion_name+'_'+str(i)+'.als')
                if emin >= int(nd['size']): 
                        if (emin==int(nd['size'])and temin<t2) or (emin > int(nd['size'])):
				                       temin=t2 
			emin = int(nd['size'])
                if emax <= int(nd['size']): 
                        if (emax==int(nd['size'])and temax<t2) or (emax < int(nd['size'])):
				                       temax=t2 
			emax = int(nd['size'])

 		print 'first wac found in: '+ nume(str(t2))+' seconds.\n-----------------------------------------------\n'
		linea='first wac found in: '+ nume(str(t2))+' seconds.\n-----------------------------------------------\n'
		rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt2/alt2_output"
		os.system(rr)
		ttotal_sin_to=ttotal_sin_to+t2
                cant_wa=cant_wa+1
	        
       	os.system('rm temp')
	i=i+1
	
   print '---------------------------------------------------'
   resultado = 'Action '+accion_name	
   resultado = resultado +' | Number of inputs processed: '+str(cant_estados)
   print resultado
   resultadof = resultado + '|'
   
   if (cant_estados>0):	
	   resultadof = resultadof + "Avg. input size: " +nume(str(float(suma_tam_lista)/float(cant_estados)))	
	   print  "Avg. input size: " +nume(str(float(suma_tam_lista)/float(cant_estados)))
           resultadof =  resultadof+ '|'

   resultadof=resultadof+'Number of workarrounds found: '+str(cant_wa)
   print 'Number of workarrounds found: '+str(cant_wa)
   resultadof = resultadof + '|'
   resultadof=resultadof+'Number of failures (exceeding a '+tiempo_to+' timeout): '+str(to)
   print 'Number of failures (exceeding a '+tiempo_to+' timeout): '+str(to)
   resultadof = resultadof + '|'
   if (cant_wa>0):
   	prome=ttotal_sin_to/float(cant_wa)
	resultadof=resultadof+'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.'
  	print 'Avg. time to find a workaround (not including failures): '+nume(str(prome))+' seconds.'
  	resultadof = resultadof + '|'
   if (cant_wa>0):
   	prome=ttotal/float(cant_wa)
	resultadof=resultadof+'Avg. time to find a workaround: '+nume(str(prome))+' seconds.'
  	print 'Avg. time to find a workaround: '+nume(str(prome))+' seconds.'
  	resultadof = resultadof + '|'
   resultadof=resultadof+'Total running time: '+nume(str(float(ttotal)))+' seconds.'
   print 'Total running time: '+nume(str(float(ttotal)))+' seconds.'
   resultadof = resultadof + '|'

   if not emin==10000:
	resultadof=resultadof+'Smallest input size: '+str(emin)+' elements.'
   	print 'Smallest input size: '+str(emin)+' elements.'
   	resultadof = resultadof + '|'
   	resultadof=resultadof+'Maximum time to find a workaround for the smallest input: '+nume(str(temin))
   	print 'Maximum time to find a workaround for the smallest input: '+nume(str(temin))

   	resultadof = resultadof + '|'
   	resultadof=resultadof+'Largest input size: '+str(emax)+' elements.'


   if not emax==-1:
   	print 'Largest input size: '+str(emax)+' elements.'
   	resultadof = resultadof + '|'
   	resultadof=resultadof+'Maximum time to find a workaround for the largest input: '+nume(str(temax))
   	print 'Maximum time to find a workaround for the largest input: '+nume(str(temax))
   	resultadof = resultadof + '|'
   print '---------------------------------------------------'	
   rr='echo "'+resultadof+'" >> ../examples/'+sys.argv[1]+'/results/alt2/alt2_output' 
   os.system(rr)
   return 	


