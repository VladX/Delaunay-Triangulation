import random
import math
n=40
print(n)
for i in xrange(n):
	print('%.18f %.18f' % (math.cos(2*i*math.pi/n), math.sin(2*i*math.pi/n)))