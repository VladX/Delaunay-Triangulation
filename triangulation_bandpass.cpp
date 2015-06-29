#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <math.h>
#include <assert.h>
using namespace std;

#ifdef DEBUG
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

/* Band pass algorithm for Delaunay triangulation. O(N log N) average, O(N^2) worst. Very fast in practice. */
class Delaunay {
public:
	struct point {
		double x, y;
		
		inline point (double x, double y) : x(x), y(y) {};
		inline point () {};
		inline bool operator== (const point & p) const { return x==p.x && y==p.y; };
		inline void operator+= (const point & p) { x+=p.x, y+=p.y; };
		inline void operator-= (const point & p) { x-=p.x, y-=p.y; };
		inline void operator/= (double s) { x/=s, y/=s; };
		inline double dist_squared (const point & p) const {
			double xx=x-p.x, yy=y-p.y;
			return xx*xx + yy*yy;
		}
		inline double dist_squared () const { return x*x + y*y; }
		inline static bool cmpByX (const point & p1, const point & p2) { return p1.x < p2.x || (p1.x == p2.x && p1.y < p2.y); }
		inline static bool cmpByY (const point & p1, const point & p2) { return p1.y < p2.y || (p1.y == p2.y && p1.x < p2.x); }
		inline static bool cmpByYrev (const point & p1, const point & p2) { return p1.y > p2.y || (p1.y == p2.y && p1.x > p2.x); }
	};
	
	struct triangle_basic {
		const point * a, * b, * c;
		
		inline triangle_basic () : a(0),b(0),c(0) {}
		
		inline triangle_basic (const point * a, const point * b, const point * c) : a(a),b(b),c(c) {}
		
		inline static double signed_area (const point & p1, const point & p2, const point & p3) {
			return (p2.x - p1.x) * (p3.y - p1.y) - (p2.y - p1.y) * (p3.x - p1.x);
		}
	};
	
	struct triangle : public triangle_basic {
		union {
			struct {
				triangle * ab, * ac, * bc;
			};
			triangle * edg[3];
		};
		point circumcentre;
		double ccRadSquared;
		
		inline triangle () : ab(0),ac(0),bc(0) {}
		
		inline triangle (const point * a, const point * b, const point * c) : triangle_basic(a, b, c),ab(0),ac(0),bc(0) {
			recache();
		}
		/* Нужно только если меняются вершины треугольника */
		inline void recache () {
			point bb = * b, cc = * c;
			bb -= * a, cc -= * a;
			double b2 = bb.dist_squared();
			double c2 = cc.dist_squared();
			circumcentre = point(cc.y * b2 - bb.y * c2, bb.x * c2 - cc.x * b2);
			circumcentre /= 2 * (bb.x * cc.y - bb.y * cc.x);
			ccRadSquared = circumcentre.dist_squared();
			circumcentre += * a;
		}
		inline void replace_edge (const triangle * from, triangle * to) {
			if (ab == from) {
				ab = to;
				return;
			}
			if (ac == from) {
				ac = to;
				return;
			}
			ASSERT(bc == from);
			bc = to;
		}
		inline const point * getOpposite (const triangle * t) const {
			if (ab == t)
				return c;
			if (ac == t)
				return b;
			ASSERT(bc == t);
			return a;
		}
		inline triangle * getEdge (const point * p, const point * q) const {
			if ((p == a && q == b) || (q == a && p == b))
				return ab;
			if ((p == a && q == c) || (q == a && p == c))
				return ac;
			ASSERT((p == b && q == c) || (q == b && p == c));
			return bc;
		}
		inline bool hasEdge (const triangle * t) const {
			if (ab == t || ac == t || bc == t)
				return true;
			return false;
		}
		inline bool checkForCorrectness () const {
			return (!ab || ab->hasEdge(this)) && (!ac || ac->hasEdge(this)) && (!bc || bc->hasEdge(this));
		}
		inline double getAngle (size_t n) const {
			double dab = a->dist_squared(* b);
			double dac = a->dist_squared(* c);
			double dbc = b->dist_squared(* c);
			if (n == 0)
				return acos((dac+dbc-dab)/(2.0*sqrt(dac)*sqrt(dbc)));
			if (n == 1)
				return acos((dab+dbc-dac)/(2.0*sqrt(dab)*sqrt(dbc)));
			return acos((dab+dac-dbc)/(2.0*sqrt(dab)*sqrt(dac)));
		}
		inline double getAngle (const triangle * t) const {
			if (ab == t)
				return getAngle((size_t) 0);
			if (ac == t)
				return getAngle((size_t) 1);
			return getAngle((size_t) 2);
		}
	};
private:
	struct edge {
		triangle * tri;
		size_t n;
		
		inline edge (triangle * t, size_t n) : tri(t), n(n) {}
		inline edge () {}
	};
	
	vector<triangle> triangles;
	vector<point> points;
	queue<edge> bad_edges;
	point root_points[3];
	const static double kPrecision;

	inline static bool delaunayCond (const edge & e) {
		triangle * opposite = e.tri->edg[e.n];
		if (!opposite)
			return true;
		const bool cond = e.tri->circumcentre.dist_squared(* opposite->getOpposite(e.tri)) * kPrecision > e.tri->ccRadSquared;
		ASSERT(cond == ((opposite->getAngle(e.tri) + e.tri->getAngle(e.n)) < M_PI));
		return cond;
	}
	
	triangle * search_triangle (const point * p) {
		triangle * t = &triangles.back();
		for (;;) {
			bool b1 = triangle::signed_area(*p, *t->a, *t->b) > 0.0;
			bool b2 = triangle::signed_area(*p, *t->b, *t->c) > 0.0;
			bool b3 = triangle::signed_area(*p, *t->c, *t->a) > 0.0;
			if (triangle::signed_area(*t->a, *t->b, *t->c) > 0.0) {
				if (b1 && b2 && b3)
					break;
				if (!b1)
					t = t->ab;
				else if (!b2)
					t = t->bc;
				else
					t = t->ac;
			}
			else {
				if (!b1 && !b2 && !b3)
					break;
				if (b1)
					t = t->ab;
				else if (b2)
					t = t->bc;
				else
					t = t->ac;
			}
		}
		return t;
	}
	
	void create_root_triangle () {
		point avg(0,0);
		for (size_t i = 0; i < points.size(); ++i)
			avg += points[i];
		avg /= points.size();
		double maxdist = 0;
		for (size_t i = 0; i < points.size(); ++i) {
			double d = avg.dist_squared(points[i]);
			if (d > maxdist)
				maxdist = d;
		}
		maxdist = sqrt(maxdist) * 1e2;
		root_points[0] = point(avg.x - maxdist * 1.732050808, avg.y - maxdist);
		root_points[1] = point(avg.x, avg.y + maxdist * 2);
		root_points[2] = point(avg.x + maxdist * 1.732050808, avg.y - maxdist);
		triangle root_tri(&root_points[0], &root_points[1], &root_points[2]);
		triangles.push_back(root_tri);
	}
	
	void remove_root_triangle () {
		for (size_t i = 0; i < triangles.size(); ++i) {
			for (size_t j = 0; j < 3; ++j) {
				triangle * t = &triangles[i];
				if (t->a == &root_points[j] || t->b == &root_points[j] || t->c == &root_points[j]) {
					if (t->ab)
						t->ab->replace_edge(t, 0);
					if (t->ac)
						t->ac->replace_edge(t, 0);
					if (t->bc)
						t->bc->replace_edge(t, 0);
					t->a = 0;
					break;
				}
			}
		}
		size_t * diff = new size_t[triangles.size()];
		size_t j = 0;
		for (size_t i = 0; i < triangles.size(); ++i) {
			diff[i] = i - j;
			if (triangles[i].a) {
				triangles[j] = triangles[i];
				++j;
			}
		}
		triangles.resize(j);
		for (size_t i = 0; i < triangles.size(); ++i) {
			triangle * t = &triangles[i];
			if (t->ab)
				t->ab -= diff[t->ab - &triangles[0]];
			if (t->ac)
				t->ac -= diff[t->ac - &triangles[0]];
			if (t->bc)
				t->bc -= diff[t->bc - &triangles[0]];
		}
		delete[] diff;
	}
	
	inline void split_triangle (const point * p, triangle * t, edge result[3]) {
		triangles.push_back(triangle(t->a, p, t->b));
		triangle * APB = &triangles.back();
		triangles.push_back(triangle(t->b, p, t->c));
		triangle * BPC = &triangles.back();
		if (t->ab)
			t->ab->replace_edge(t, APB);
		if (t->bc)
			t->bc->replace_edge(t, BPC);
		t->b = p;
		APB->ab = t;
		APB->ac = t->ab;
		APB->bc = BPC;
		BPC->ab = APB;
		BPC->ac = t->bc;
		BPC->bc = t;
		t->ab = APB;
		t->bc = BPC;
		t->recache();
		result[0] = edge(APB, 1), result[1] = edge(BPC, 1), result[2] = edge(t, 1);
	}
	
	inline void flip (const edge & e, triangle * ret[2]) {
		const triangle top = * e.tri->edg[e.n], bottom = * e.tri; // bottom to right, top to left
		triangle * left = e.tri->edg[e.n], * right = e.tri;
		const point * D = top.getOpposite(right);
		if (e.n == 0) {
			left->a = bottom.c;
			left->b = bottom.b;
			left->c = D;
			left->ab = bottom.bc;
			left->ac = right;
			left->bc = top.getEdge(bottom.b, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.a;
			right->c = bottom.c;
			right->ab = top.getEdge(bottom.a, D);
			right->ac = left;
			right->bc = bottom.ac;
			if (right->ab)
				right->ab->replace_edge(left, right);
		}
		else if (e.n == 1) {
			left->a = bottom.b;
			left->b = bottom.c;
			left->c = D;
			left->ab = bottom.bc;
			left->ac = right;
			left->bc = top.getEdge(bottom.c, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.a;
			right->c = bottom.b;
			right->ab = top.getEdge(bottom.a, D);
			right->ac = left;
			right->bc = bottom.ab;
			if (right->ab)
				right->ab->replace_edge(left, right);
		}
		else {
			left->a = bottom.a;
			left->b = bottom.c;
			left->c = D;
			left->ab = bottom.ac;
			left->ac = right;
			left->bc = top.getEdge(bottom.c, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.b;
			right->c = bottom.a;
			right->ab = top.getEdge(bottom.b, D);
			right->ac = left;
			right->bc = bottom.ab;
			if (right->ab)
				right->ab->replace_edge(left, right);
		}
		left->recache();
		right->recache();
		ret[0] = left, ret[1] = right;
	}
	
	void next_point (const point * p) {
		triangle * t = search_triangle(p);
		ASSERT(t->checkForCorrectness());
		edge res[3];
		split_triangle(p, t, res);
		bad_edges.push(res[0]), bad_edges.push(res[1]), bad_edges.push(res[2]);
		while (!bad_edges.empty()) {
			edge e = bad_edges.front();
			bad_edges.pop();
			if (delaunayCond(e))
				continue;
			triangle * ret[2];
			flip(e, ret);
			for (size_t j = 0; j < 2; ++j) {
				if (ret[j]->c == p)
					bad_edges.push(edge(ret[j], 0));
				else if (ret[j]->b == p)
					bad_edges.push(edge(ret[j], 1));
				else if (ret[j]->a == p)
					bad_edges.push(edge(ret[j], 2));
			}
		}
	}
	
	bool check_triangulation () const {
		for (size_t i = 0; i < triangles.size(); ++i) {
			const triangle & t = triangles[i];
			for (size_t j = 0; j < points.size(); ++j) {
				const point * p = &points[j];
				if (p == t.a || p == t.b || p == t.c)
					continue;
				if (t.circumcentre.dist_squared(* p) < t.ccRadSquared)
					return false;
			}
		}
		return true;
	}
	
	void ensure_proper_ordering () {
		sort(points.begin(), points.end(), point::cmpByX);
		const size_t M = sqrt((double) points.size()) * 0.5;
		if (M == 0)
			return;
		const size_t step = points.size() / M;
		for (size_t i = 0; i < M; ++i)
			sort(points.begin() + step * i, points.begin() + step * (i + 1), (i & 1) ? point::cmpByYrev : point::cmpByY);
		sort(points.begin() + step * M, points.end(), (M & 1) ? point::cmpByYrev : point::cmpByY);
	}
public:
	inline void add_point (double x, double y) {
		points.push_back(point(x, y));
	}
	
	void build () {
		if (points.size() < 2)
			return;
		ensure_proper_ordering();
		triangles.reserve(points.size() * 2 + 4); // Euler: V-E+F=2
		create_root_triangle();
		for (size_t i = 0; i < points.size(); ++i)
			next_point(&points[i]);
		ASSERT(check_triangulation());
		remove_root_triangle();
	}
	
	inline vector<triangle> & getTriangles () {
		return triangles;
	}
};

const double Delaunay::kPrecision = 1.0 + 1e-8;

int main () {
	cin.sync_with_stdio(false);
	cout.sync_with_stdio(false);
	Delaunay d;
	int n;
	cin>>n;
	for (int i=0;i<n;++i) {
		double x,y;
		cin>>x>>y;
		d.add_point(x, y);
	}
	d.build();
	auto t=d.getTriangles();
	size_t cnt=t.size()*3;
	cout<<cnt<<endl;
	for (auto x : t) {
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.b->x<<' '<<x.b->y<<endl;
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
		cout<<x.b->x<<' '<<x.b->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
	}
	return 0;
}