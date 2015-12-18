/*
Copyright (c) 2015 Vladislav Samsonov <vvladxx@gmail.com>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

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
	struct history_node;
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
	};
	
	struct triangle_basic {
		const point * a, * b, * c;
		
		inline triangle_basic () : a(0),b(0),c(0) {}
		
		inline triangle_basic (const point * a, const point * b, const point * c) : a(a),b(b),c(c) {}
		
		inline static double signed_area (const point & p1, const point & p2, const point & p3) {
			return (p2.x - p1.x) * (p3.y - p1.y) - (p2.y - p1.y) * (p3.x - p1.x);
		}
		
		inline bool is_inside (const point & p) const {
			double s1 = signed_area(p, * a, * b);
			double s2 = signed_area(p, * b, * c);
			double s3 = signed_area(p, * c, * a);
			if ((s1 < 0 && s2 < 0 && s3 < 0) || (s1 > 0 && s2 > 0 && s3 > 0))
				return true;
			if (s1 == 0) {
				if ((s2 < 0 && s3 < 0) || (s2 > 0 && s3 > 0))
					return true;
				return false;
			}
			if (s2 == 0) {
				if ((s1 < 0 && s3 < 0) || (s1 > 0 && s3 > 0))
					return true;
				return false;
			}
			if (s3 == 0) {
				if ((s1 < 0 && s2 < 0) || (s1 > 0 && s2 > 0))
					return true;
				return false;
			}
			return false;
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
		size_t graphnode;
		
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
	
	struct history_node {
		triangle_basic tri;
		triangle * link;
		size_t nodes[3];
		
		inline history_node () {}
		inline history_node (triangle * t) : tri(* t), link(t) {
			nodes[0] = 0, nodes[1] = 0, nodes[2] = 0;
		}
	};
	
	vector<triangle> triangles;
	vector<point> points;
	point root_points[3];
	vector<history_node> history_nodes;
	queue<edge> bad_edges;
	const static double kPrecision;
	
	inline static bool delaunay_cond (const edge & e) {
		triangle * opposite = e.tri->edg[e.n];
		if (!opposite)
			return true;
		const bool cond = e.tri->circumcentre.dist_squared(* opposite->get_opposite(e.tri)) * kPrecision > e.tri->ccRadSquared;
		return cond;
	}
	
	/* For flip */
	inline void advance (triangle * t1, triangle * t2) {
		size_t n1 = history_nodes.size();
		size_t n2 = n1 + 1;
		history_nodes.push_back(history_node(t1));
		history_nodes.push_back(history_node(t2));
		history_nodes[t1->graphnode].nodes[0] = n1;
		history_nodes[t1->graphnode].nodes[1] = n2;
		history_nodes[t2->graphnode].nodes[0] = n1;
		history_nodes[t2->graphnode].nodes[1] = n2;
		t1->graphnode = n1;
		t2->graphnode = n2;
	}
	
	/* For split */
	inline void advance (size_t node, triangle * t1, triangle * t2, triangle * t3) {
		history_node * n = &history_nodes[node];
		n->nodes[0] = history_nodes.size();
		n->nodes[1] = history_nodes.size() + 1;
		n->nodes[2] = history_nodes.size() + 2;
		history_nodes.push_back(history_node(t1));
		history_nodes.push_back(history_node(t2));
		history_nodes.push_back(history_node(t3));
		n = &history_nodes[node];
		t1->graphnode = n->nodes[0];
		t2->graphnode = n->nodes[1];
		t3->graphnode = n->nodes[2];
	}
	
	triangle * search_triangle (const point * p) const {
		const history_node * n = &history_nodes.front();
		while (n->nodes[0]) {
			if (history_nodes[n->nodes[0]].tri.is_inside(* p)) {
				n = &history_nodes[n->nodes[0]];
				continue;
			}
			if (history_nodes[n->nodes[1]].tri.is_inside(* p)) {
				n = &history_nodes[n->nodes[1]];
				continue;
			}
			ASSERT(history_nodes[n->nodes[2]].tri.is_inside(* p));
			n = &history_nodes[n->nodes[2]];
		}
		return n->link;
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
		maxdist = sqrt(maxdist) * 1e2;
		root_points[0] = point(avg.x - maxdist * 1.732050808, avg.y - maxdist);
		root_points[1] = point(avg.x, avg.y + maxdist * 2);
		root_points[2] = point(avg.x + maxdist * 1.732050808, avg.y - maxdist);
		triangle root_tri(&root_points[0], &root_points[1], &root_points[2]);
		root_tri.graphnode = 0; // link root triangle with first node in history graph
		triangles.push_back(root_tri);
		history_nodes.push_back(history_node(&triangles.front()));
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
		advance(t->graphnode, APB, BPC, t);
		result[0] = edge(APB, 1), result[1] = edge(BPC, 1), result[2] = edge(t, 1);
	}
	
	inline void flip (const edge & e, triangle * ret[2]) {
		const triangle top = * e.tri->edg[e.n], bottom = * e.tri; // bottom to right, top to left
		triangle * left = e.tri->edg[e.n], * right = e.tri;
		const point * D = top.get_opposite(right);
		if (e.n == 0) {
			left->a = bottom.c;
			left->b = bottom.b;
			left->c = D;
			left->ab = bottom.bc;
			left->ac = right;
			left->bc = top.get_edge(bottom.b, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.a;
			right->c = bottom.c;
			right->ab = top.get_edge(bottom.a, D);
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
			left->bc = top.get_edge(bottom.c, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.a;
			right->c = bottom.b;
			right->ab = top.get_edge(bottom.a, D);
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
			left->bc = top.get_edge(bottom.c, D);
			if (left->ab)
				left->ab->replace_edge(right, left);
			right->a = D;
			right->b = bottom.b;
			right->c = bottom.a;
			right->ab = top.get_edge(bottom.b, D);
			right->ac = left;
			right->bc = bottom.ab;
			if (right->ab)
				right->ab->replace_edge(left, right);
		}
		left->recache();
		right->recache();
		advance(left, right);
		ret[0] = left, ret[1] = right;
	}
	
	void next_point (const point * p) {
		triangle * t = search_triangle(p);
		ASSERT(t->check_for_correctness());
		edge res[3];
		split_triangle(p, t, res);
		bad_edges.push(res[0]), bad_edges.push(res[1]), bad_edges.push(res[2]);
		while (!bad_edges.empty()) {
			edge e = bad_edges.front();
			bad_edges.pop();
			if (delaunay_cond(e))
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
	inline void add_point (double x, double y) {
		points.push_back(point(x, y));
	}
	
	void build () {
		if (points.size() < 2)
			return;
		triangles.reserve(points.size() * 2 + 4); // Euler: V-E+F=2
		create_root_triangle();
		random_shuffle(points.begin(), points.end());
		for (size_t i = 0; i < points.size(); ++i)
			next_point(&points[i]);
		ASSERT(check_triangulation());
		remove_root_triangle();
	}
	
	inline vector<triangle> & get_triangles () {
		return triangles;
	}
	/* Найти треугольник, содержащий точку (x, y). O(log N) */
	inline triangle * locate_point (double x, double y) const {
		const point p(x, y);
		return search_triangle(&p);
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
	/*for (auto x : t) {
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.b->x<<' '<<x.b->y<<endl;
		cout<<x.a->x<<' '<<x.a->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
		cout<<x.b->x<<' '<<x.b->y<<' '<<x.c->x<<' '<<x.c->y<<endl;
	}*/
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