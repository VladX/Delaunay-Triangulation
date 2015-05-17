from PIL import Image
from PIL import ImageDraw

f=open('tri.txt','r')
n=int(f.readline())
maxx=float('-inf')
maxy=float('-inf')
minx=float('+inf')
miny=float('+inf')
coord=[]
for i in xrange(n):
	ax,ay,bx,by=map(float,f.readline().split())
	maxx=max(maxx,ax)
	minx=min(minx,ax)
	maxy=max(maxy,ay)
	miny=min(miny,ay)
	maxx=max(maxx,bx)
	minx=min(minx,bx)
	maxy=max(maxy,by)
	miny=min(miny,by)
	coord.append((ax,ay))
	coord.append((bx,by))
width=1200
height=int((width/(maxx-minx))*(maxy-miny))
stepx=(width-10)/(maxx-minx)
stepy=(height-10)/(maxy-miny)
im = Image.new("RGB", (width, height), "white")
draw = ImageDraw.Draw(im)
for c in coord:
	draw.ellipse((5+stepx*(c[0]-minx)-5,5+stepy*(c[1]-miny)-5,5+stepx*(c[0]-minx)+5,5+stepy*(c[1]-miny)+5),fill='blue')
f=open('tri.txt','r')
n=int(f.readline())
for i in xrange(n):
	ax,ay,bx,by=map(float,f.readline().split())
	draw.line((5+stepx*(ax-minx),5+stepy*(ay-miny),5+stepx*(bx-minx),5+stepy*(by-miny)),fill='black')
im.transpose(Image.FLIP_TOP_BOTTOM).save('out.png','png')