from timeout import timeout
import time
# Timeout after 5 seconds




@timeout()
def call_with_timeout(funcion, parametro):
     t=time.time()
     try:		
        funcion(parametro)
        return [time.time()-t,False]
     except:
	return [time.time()-t,True]

def corre(i):
    	while i<1000000000:
		print i
		i=i+1
      
# Timeout after 30 seconds, with the error "Connection timed out"
#@timeout(30, os.strerror(errno.ETIMEDOUT))
#def long_running_function3():
#    



print call_with_timeout(corre,0)

