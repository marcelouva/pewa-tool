from functools import wraps
import errno
import os
import signal,time

class TimeoutError(Exception):
    pass

def timeout(seconds=600, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
	    print 'termino'
            raise TimeoutError(error_message)

        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wraps(func)(wrapper)

    return decorator




#la funcion corre y corta la corrida en 10 minutos. retorna un par con el tiempo y un booleano indicando si salio por timeouto o no
@timeout()
def call_with_timeout(funcion, parametro1, parametro2,filename):
     t=time.time()
     try:		
        funcion(parametro1,parametro2,filename)
        return [time.time()-t,False]
     except:
	return [time.time()-t,True]



@timeout()
def call_with_timeout_permament(funcion, parametro1):
     t=time.time()
     try:	
        funcion(parametro1)

        return [time.time()-t,False]
     except:
	return [time.time()-t,True]


'''def corre(i,j):
    	while i<1000000000:
		print i
		i=i+1
		print j
      



print call_with_timeout(corre,0,8)
'''
