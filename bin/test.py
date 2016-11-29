import os,incrementalwa,timeout,new_generate_alt1

ac='borrar'
ur=2

time_of= timeout.call_with_timeout(incrementalwa.run_incremental_alloy, 'resultado.als',100,'wac_'+ac+'_with_'+str(ur)+'.list')
print time_of
#wac_list = new_generate_alt1.traer_pres_desde_archivo('wac_'+accion+'_with_'+str(unroll)+'.list') 
#print wac_list 
