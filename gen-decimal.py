import random
n = 400000
A = 1000000
print(n)
for i in xrange(n):
	print('%d %d' % (random.randrange(A),random.randrange(A)))