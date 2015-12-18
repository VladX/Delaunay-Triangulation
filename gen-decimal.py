import random
n = 100
A = 10000
print(n)
for i in xrange(n):
	print('%d %d' % (random.randrange(A),random.randrange(A)))