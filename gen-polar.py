import random
import math
n = 200
print(n)
for i in xrange(n):
	R, phi = math.sqrt(random.random()), 2*math.pi*random.random()
	print('%.12f %.12f' % (R*math.cos(phi), R*math.sin(phi)))