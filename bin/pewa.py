import os,sys,glob,new2_generate_alt1,generate_alt2,ap1
from sets import Set


if len(sys.argv)==3:
	print 'Error: missing parameters.'
	print 'Use: python generate.py <case_study> <action_fix> <method>. Method is 1 or 2.'
else:
   
   casos_de_studio= os.listdir('../examples')
   tiempo_to = ap1.read_config_case("../config.ini","options")['timeout']
   input_file = ap1.read_config_case("../config.ini","options")['input_file']
   if sys.argv[3]=='1':
        	
	if sys.argv[1] in casos_de_studio:
                
	        lista_ac = glob.glob('../examples/'+sys.argv[1]+'/actions/*_act')
		cade="cat ../examples/"+sys.argv[1]+"/actions/preludio "+" ".join(lista_ac)+" > temporalnew.dals"
		os.system(cade)
                

         	if not "../examples/"+sys.argv[1]+"/actions/"+sys.argv[2]+"_act" in lista_ac:
			print 'Error : not found action '+sys.argv[2]
		else:

			info=new2_generate_alt1.read_action(sys.argv[1])
                        
			parametros_de_retorno=info['../examples/'+sys.argv[1]+'/actions/'+sys.argv[2]+'_act'][8]
			pp="["+",".join(list(info['parametros_dyn']))+"]"
	
			acts=info.keys()
			pin=info['../examples/'+sys.argv[1]+'/actions/'+sys.argv[2]+'_act'][6]
			scope =info['../examples/'+sys.argv[1]+'/actions/'+sys.argv[2]+'_act'][7]

			acts.remove('parametros_dyn')

			one_sig_actions= "\n".join(info['one_sig_actions'])
			acts.remove('one_sig_actions')
		        
			if("../examples/"+sys.argv[1]+"/actions/"+sys.argv[2]+"_act" in acts):
     			    	p=info["../examples/"+sys.argv[1]+"/actions/"+sys.argv[2]+"_act"]
			        
	    			precondicion_accion_rota=p[5]	
	    			poscondicion_negada=p[0]
     	    		        del acts[acts.index("../examples/"+sys.argv[1]+"/actions/"+sys.argv[2]+"_act")]
				lis=[]	

				#add_to_set[s:set univ,n:univ]
				
				for elem in acts:
					cade_add_set=''
					v=info[elem][3]
					
					if len(parametros_de_retorno)>1:
						v= v[:len(v)-1]
						#si la la cant de parametros de retorno es > 1 retornos enteros 32 
						if ("return_intJ_1" in info[elem][8] or "return_intJ_1'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_1]'
						
						if ("return_intJ_2" in info[elem][8] or "return_intJ_2'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_2]'
						
						if ("return_intJ_3" in info[elem][8] or "return_intJ_3'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_3]'

						if ("return_intJ_4" in info[elem][8] or "return_intJ_4'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_4]'


	
						v=v+cade_add_set+')'

					
						
		 				

			        	lis.append(v)
				r="+".join(lis)
				prog=''

 			     
				#sys.exit(0)
				if len(parametros_de_retorno)>1:

					if ('return_intJ_1' in parametros_de_retorno) or ('return_intJ_2' in parametros_de_retorno) or ('return_intJ_3' in parametros_de_retorno)or ('return_intJ_4' in parametros_de_retorno):
						prog=prog+'init_set[set_intJ];'
						
					
				prog=prog+'valid_intA:=false;valid_bool:=false;valid_intJ:=false;('+ r +')*'		
                   
	    			cuerpo='pre={'+precondicion_accion_rota+'}\nprogram={'+prog+'}\n post={'+poscondicion_negada+'}\n'
			        asercion=one_sig_actions+'\nassertCorrectness programa_wap'+pp+'{'+cuerpo+'}\n'+p[1]+'\n'+'check programa_wap\n'

			else:
				 print 'Error: action '+sys.argv[2]+' not available.'	
         			 asercion=''

			if len(asercion)==0:
				print 'Error: action.'
			else:
				f = open('temporalnew.dals', "a")
                                    				
				f.write(asercion)
				f.close()
			
			
                        if (sys.argv[1]=='jodatime'):
			   
                            
			    result=generate_alt1.fix_alt1_jodatime(sys.argv[1],sys.argv[2],pin,tiempo_to,input_file)
			    	
			else: 
			    result=new2_generate_alt1.fix_alt1(sys.argv[1],sys.argv[2],pin,tiempo_to,input_file,True)

			linea=sys.argv[2]+':'+result[-1]+'\n'
			rr="echo '"+linea+"' >> ../examples/"+sys.argv[1]+"/results/alt1/alt1_output"
					
			os.system(rr)

   if sys.argv[3]=='2':	
	if sys.argv[1] in casos_de_studio:
		info=generate_alt2.generate_fact_alt_2('../examples/'+sys.argv[1]+'/actions/'+sys.argv[2]+'_act')
		cadeQF=info[len(info)-1]
		generate_alt2.fix_a2(sys.argv[1],info[0],info[1],info[2],sys.argv[2],cadeQF,tiempo_to,input_file)
		






