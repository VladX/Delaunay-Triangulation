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

/* Delaunay triangulation O(N log N) */
class Delaunay {
private:
	struct bucket_node;
public:
	struct point {
		double x, y;
		
		inline point (double x, double y) : x(x), y(y) {};
		inline point () {};
		inline bool operator== (const point & p) const { return x==p.x && y==p.y; };
		inline void operator+= (const point & p) { x+=p.x, y+=p.y; };
		inline void operator-= (const point & p) { x-=p.x, y-=p.y; };
		inline void operator/= (double s) { x/=s, y/=s; };
		inline void operator*= (double s) { x*=s, y*=s; };
		inline double dist_squared (const point & p) const { double xx=x-p.x, yy=y-p.y; return xx*xx + yy*yy; }
		inline double dist_squared () const { return x*x + y*y; }
		inline static bool cmpByX (const point & p1, const point & p2) { return p1.x < p2.x || (p1.x == p2.x && p1.y < p2.y); }
		inline static bool cmpByY (const point & p1, const point & p2) { return p1.y < p2.y || (p1.y == p2.y && p1.x < p2.x); }
		inline bool operator< (const point & p2) const { return x < p2.x || (x == p2.x && y < p2.y); }
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
		bucket_node * bucket;
		
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
			double det = bb.x * cc.y - bb.y * cc.x;
			if (det == 0) { // треугольник вырожденный (все точки на одной прямой)
				circumcentre = point(0, 0);
				ccRadSquared = INFINITY;
			}
			else {
				circumcentre = point(cc.y * b2 - bb.y * c2, bb.x * c2 - cc.x * b2);
				circumcentre /= 2 * det;
				ccRadSquared = circumcentre.dist_squared();
				circumcentre += * a;
			}
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
		
		inline const point * get_opposite (const triangle * t) const {
			if (ab == t)
				return c;
			if (ac == t)
				return b;
			ASSERT(bc == t);
			return a;
		}
		
		inline triangle * get_incident_edge (const triangle * t, const point * p) const {
			if (ab == t)
				return (a == p) ? ac : bc;
			if (ac == t)
				return (a == p) ? ab : bc;
			return (b == p) ? ab : ac;
		}
		
		inline triangle * get_edge (const point * p, const point * q) const {
			if ((p == a && q == b) || (q == a && p == b))
				return ab;
			if ((p == a && q == c) || (q == a && p == c))
				return ac;
			ASSERT((p == b && q == c) || (q == b && p == c));
			return bc;
		}
		
		inline bool has_edge (const triangle * t) const {
			if (ab == t || ac == t || bc == t)
				return true;
			return false;
		}
		
		inline bool check_for_correctness () const {
			return (!ab || ab->has_edge(this)) && (!ac || ac->has_edge(this)) && (!bc || bc->has_edge(this));
		}
	};
private:
	struct edge {
		triangle * tri;
		size_t n;
		
		inline edge (triangle * t, size_t n) : tri(t), n(n) {}
		inline edge () {}
	};
	
	struct bucket_node {
		const point * p;
		bucket_node * next;
	};
	
	vector<triangle> triangles;
	vector<point> points;
	point root_points[3];
	vector<edge> bad_edges;
	bucket_node * buckets; // Вершины, ассоциированные с треугольниками
	triangle ** locations; // Треугольники, ассоциированные с вершинами
	const static double kPrecision;
	
	/*inline bool incircle (point pa, point pb, point pc, point pd) const {
		if (triangle::signed_area(pa, pb, pc) > 0)
			swap(pb, pc);
		double adx = pa.x - pd.x, bdx = pb.x - pd.x, cdx = pc.x - pd.x, ady = pa.y - pd.y, bdy = pb.y - pd.y, cdy = pc.y - pd.y;
		double bdxcdy = bdx * cdy, cdxbdy = cdx * bdy;
		double alift = adx * adx + ady * ady;
		double cdxady = cdx * ady, adxcdy = adx * cdy;
		double blift = bdx * bdx + bdy * bdy;
		double adxbdy = adx * bdy, bdxady = bdx * ady;
		double clift = cdx * cdx + cdy * cdy;
		double det = alift * (bdxcdy - cdxbdy) + blift * (cdxady - adxcdy) + clift * (adxbdy - bdxady);
		double permanent = (fabs(bdxcdy) + fabs(cdxbdy)) * alift + (fabs(cdxady) + fabs(adxcdy)) * blift + (fabs(adxbdy) + fabs(bdxady)) * clift;
		double errbound = iccerrboundA * permanent;
		if ((det > errbound) || (-det > errbound))
			return det >= 0;
		return incircleadapt(pa, pb, pc, pd, permanent);
	}*/
	
	inline bool is_root (const point * p) const {
		if (p == &root_points[0] || p == &root_points[1] || p == &root_points[2])
			return true;
		return false;
	}
	
	inline bool delaunay_cond (const edge & e) const {
		triangle * opposite = e.tri->edg[e.n];
		if (!opposite)
			return true;
		if (e.tri->ccRadSquared == INFINITY || opposite->ccRadSquared == INFINITY)
			return false;
		const point * op = opposite->get_opposite(e.tri);
		const bool ra = is_root(e.tri->a), rb = is_root(e.tri->b), rc = is_root(e.tri->c), ro = is_root(op);
		if (ra + rb + rc + ro == 1) {
			if (ro)
				return true;
			if (e.n == 0) {
				if (rc)
					return true;
				if (ra)
					return triangle::signed_area(*op, *e.tri->c, *e.tri->b) >= 0;
				if (rb)
					return triangle::signed_area(*op, *e.tri->a, *e.tri->c) >= 0;
			}
			else if (e.n == 1) {
				if (rb)
					return true;
				if (ra)
					return triangle::signed_area(*op, *e.tri->c, *e.tri->b) >= 0;
				if (rc)
					return triangle::signed_area(*op, *e.tri->b, *e.tri->a) >= 0;
			}
			else {
				if (ra)
					return true;
				if (rb)
					return triangle::signed_area(*op, *e.tri->a, *e.tri->c) >= 0;
				if (rc)
					return triangle::signed_area(*op, *e.tri->b, *e.tri->a) >= 0;
			}
		}
		const bool cond = e.tri->circumcentre.dist_squared(* op) * kPrecision > e.tri->ccRadSquared;
		return cond;
	}
	
	void create_root_triangle () {
		point bb_min = points[0], bb_max = points[0];
		for (size_t i = 1; i < points.size(); ++i) {
			if (points[i].x < bb_min.x)
				bb_min.x = points[i].x;
			else if (points[i].x > bb_max.x)
				bb_max.x = points[i].x;
			if (points[i].y < bb_min.y)
				bb_min.y = points[i].y;
			else if (points[i].y > bb_max.y)
				bb_max.y = points[i].y;
		}
		point avg = bb_min;
		avg += bb_max;
		avg /= 2;
		double maxdist = 0;
		for (size_t i = 0; i < points.size(); ++i) {
			double d = avg.dist_squared(points[i]);
			if (d > maxdist)
				maxdist = d;
		}
		maxdist = sqrt(maxdist) * 1.5;
		root_points[0] = point(avg.x, avg.y + maxdist * 2);
		root_points[1] = point(avg.x - maxdist * 2, avg.y - maxdist);
		root_points[2] = point(avg.x + maxdist * 2, avg.y - maxdist);
		triangle root_tri(&root_points[0], &root_points[1], &root_points[2]);
		root_tri.bucket = buckets;
		triangles.push_back(root_tri);
		for (size_t i = 0; i < points.size(); ++i) {
			buckets[i].p = &points[i];
			buckets[i].next = (i + 1 < points.size()) ? &buckets[i + 1] : 0;
			locations[i] = triangles.data();
		}
	}
	
	void remove_root_triangle () {
		for (size_t i = 0; i < triangles.size(); ++i) {
			triangle * t = &triangles[i];
			if (is_root(t->a) || is_root(t->b) || is_root(t->c)) {
				if (t->ab)
					t->ab->replace_edge(t, 0);
				if (t->ac)
					t->ac->replace_edge(t, 0);
				if (t->bc)
					t->bc->replace_edge(t, 0);
				t->a = 0;
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
		triangles.push_back(triangle(t->a, t->b, p));
		triangle * ABP = &triangles.back();
		triangles.push_back(triangle(t->b, t->c, p));
		triangle * BCP = &triangles.back();
		if (t->ab)
			t->ab->replace_edge(t, ABP);
		if (t->bc)
			t->bc->replace_edge(t, BCP);
		t->b = p;
		ABP->ab = t->ab, ABP->ac = t, ABP->bc = BCP;
		BCP->ab = t->bc, BCP->ac = ABP, BCP->bc = t;
		t->ab = ABP;
		t->bc = BCP;
		t->recache();
		bucket_node * b1 = 0, * b2 = 0, * b3 = 0;
		for (bucket_node * b = t->bucket, * nxt; b; b = nxt) {
			nxt = b->next;
			if (triangle::signed_area(*b->p, *p, *ABP->a) >= 0 && triangle::signed_area(*b->p, *ABP->b, *p) >= 0) {
				b->next = b1;
				b1 = b;
				locations[b->p - points.data()] = ABP;
			}
			else if (triangle::signed_area(*b->p, *BCP->b, *p) > 0) {
				b->next = b2;
				b2 = b;
				locations[b->p - points.data()] = BCP;
			}
			else {
				b->next = b3;
				b3 = b;
				locations[b->p - points.data()] = t;
			}
		}
		ABP->bucket = b1, BCP->bucket = b2, t->bucket = b3;
		result[0] = edge(ABP, 0), result[1] = edge(BCP, 0), result[2] = edge(t, 1);
	}
	
	inline void flip (const edge & e, triangle * ret[2]) {
		const triangle top = * e.tri->edg[e.n], bottom = * e.tri; // bottom to right, top to left
		triangle * left = e.tri->edg[e.n], * right = e.tri;
		const point * D = top.get_opposite(right);
		if (e.n == 0) {
			left->a = bottom.b, left->b = bottom.c, left->c = D;
			left->ab = bottom.bc;
			left->ac = top.get_edge(bottom.b, D);
			left->bc = right;
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D, right->b = bottom.c, right->c = bottom.a;
			right->ab = left;
			right->ac = top.get_edge(bottom.a, D);
			right->bc = bottom.ac;
			if (right->ac)
				right->ac->replace_edge(left, right);
		}
		else if (e.n == 1) {
			left->a = bottom.a, left->b = bottom.b, left->c = D;
			left->ab = bottom.ab;
			left->ac = top.get_edge(bottom.a, D);
			left->bc = right;
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D, right->b = bottom.b, right->c = bottom.c;
			right->ab = left;
			right->ac = top.get_edge(bottom.c, D);
			right->bc = bottom.bc;
			if (right->ac)
				right->ac->replace_edge(left, right);
		}
		else {
			left->a = bottom.c, left->b = bottom.a, left->c = D;
			left->ab = bottom.ac;
			left->ac = top.get_edge(bottom.c, D);
			left->bc = right;
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D, right->b = bottom.a, right->c = bottom.b;
			right->ab = left;
			right->ac = top.get_edge(bottom.b, D);
			right->bc = bottom.ab;
			if (right->ac)
				right->ac->replace_edge(left, right);
		}
		left->recache();
		right->recache();
		bucket_node * b1 = 0, * b2 = 0;
		for (bucket_node * b = left->bucket, * nxt; b; b = nxt) {
			nxt = b->next;
			if (triangle::signed_area(*left->b, *left->c, *b->p) > 0) {
				b->next = b1;
				b1 = b;
				locations[b->p - points.data()] = left;
			}
			else {
				b->next = b2;
				b2 = b;
				locations[b->p - points.data()] = right;
			}
		}
		for (bucket_node * b = right->bucket, * nxt; b; b = nxt) {
			nxt = b->next;
			if (triangle::signed_area(*left->b, *left->c, *b->p) > 0) {
				b->next = b1;
				b1 = b;
				locations[b->p - points.data()] = left;
			}
			else {
				b->next = b2;
				b2 = b;
				locations[b->p - points.data()] = right;
			}
		}
		left->bucket = b1;
		right->bucket = b2;
		ret[0] = left, ret[1] = right;
	}
	
	void next_point (const point * p, triangle * t) {
		ASSERT(t->check_for_correctness());
		edge res[3];
		split_triangle(p, t, res);
		bad_edges.push_back(res[0]), bad_edges.push_back(res[1]), bad_edges.push_back(res[2]);
		while (!bad_edges.empty()) {
			edge e = bad_edges.back();
			bad_edges.pop_back();
			if (delaunay_cond(e))
				continue;
			triangle * ret[2];
			flip(e, ret);
			for (size_t j = 0; j < 2; ++j) {
				if (ret[j]->c == p)
					bad_edges.push_back(edge(ret[j], 0));
				else if (ret[j]->b == p)
					bad_edges.push_back(edge(ret[j], 1));
				else if (ret[j]->a == p)
					bad_edges.push_back(edge(ret[j], 2));
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
				if (t.circumcentre.dist_squared(* p) * kPrecision < t.ccRadSquared)
					return false;
			}
		}
		return true;
	}
	
	inline size_t index_by_ptr (const point * p) const {
		return p - points.data();
	}
	
	inline void walk_counterclockwise (vector<bool> & used, vector< vector<const point *> > & vor, const point * around, const triangle * cur, const triangle * prev, const triangle * t) const {
		size_t idx = index_by_ptr(around);
		used[idx] = true;
		for (;;) {
			if (!cur) {
				vor[idx].clear();
				break;
			}
			vor[idx].push_back(&cur->circumcentre);
			if (cur == t)
				break;
			const triangle * tmp = cur->get_incident_edge(prev, around);
			prev = cur, cur = tmp;
		}
	}
public:
	inline Delaunay () : buckets(0), locations(0) {}
	
	inline ~Delaunay () {
		if (buckets) {
			delete[] buckets;
			delete[] locations;
		}
	}
	
	inline void add_point (double x, double y) {
		points.push_back(point(x, y));
	}
	
	inline void add_point (const point & p) {
		points.push_back(p);
	}
	
	void build () {
		if (points.size() < 2)
			return;
		triangles.reserve(points.size() * 2 + 4); // Euler: V-E+F=2
		random_shuffle(points.begin(), points.end());
		buckets = new bucket_node[points.size()];
		locations = new triangle *[points.size()];
		create_root_triangle();
		for (size_t i = 0; i < points.size(); ++i)
			next_point(&points[i], locations[i]);
		ASSERT(check_triangulation());
		remove_root_triangle();
	}
	
	inline vector<triangle> & get_triangles () {
		return triangles;
	}
	/* Построить многоугольники диаграммы Вороного по триангуляции */
	void build_voronoi_cells (vector< vector<const point *> > & vor) const {
		vector<bool> used(points.size());
		vor.resize(points.size());
		for (size_t i = 0; i < triangles.size(); ++i) {
			const triangle * t = &triangles[i];
			if (!used[index_by_ptr(t->a)])
				walk_counterclockwise(used, vor, t->a, triangle::signed_area(*t->a, *t->b, *t->c) > 0 ? t->ac : t->ab, t, t);
			if (!used[index_by_ptr(t->b)])
				walk_counterclockwise(used, vor, t->b, triangle::signed_area(*t->a, *t->b, *t->c) > 0 ? t->ab : t->bc, t, t);
			if (!used[index_by_ptr(t->c)])
				walk_counterclockwise(used, vor, t->c, triangle::signed_area(*t->a, *t->b, *t->c) > 0 ? t->bc : t->ac, t, t);
		}
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
	auto t=d.get_triangles();
	size_t cnt=t.size()*3;
	cout<<cnt<<endl;
	for (auto x : t) {
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.b->x<<' '<<x.b->y<<endl;
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
		cout<<x.b->x<<' '<<x.b->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
	}
	/*Delaunay d;
	for (;;) {
		double x,y;
		if (!cin.good()) break;
		cin>>x;
		if (!cin.good()) break;
		cin>>y;
		d.add_point(x, y);
	}
	d.build();
	double answer=0;
	size_t ans=0;
	vector< vector<const Delaunay::point *> > cells;
	d.build_voronoi_cells(cells);
	for (size_t i = 0; i < cells.size(); ++i)
		if (cells[i].size())
			answer += cells[i].size(), ++ans;
	cout<<(ans==0 ? 0 : (answer/ans))<<endl;*/
	return 0;
}