def calcula(a,b,k):
        print 'K='+str(k)			
	print str(a)+':'+str(b)
	seg=(b+k)%60
	if(b+k>=0) and (b+k<60):
	    hora=a
	else:	
            hora=((abs(k)+60+b)/60)
	    if(k>=0):
		hora=hora-1
            else:
		hora=0-hora
	    print 'hora '+str(hora)	
            hora=(a+hora)%24
	
	print str(hora)+':'+str(seg)
	print '.....................'

calcula(10,3,-2)
calcula(0,0,-10)
calcula(10,3,2)
calcula(10,3,80)
