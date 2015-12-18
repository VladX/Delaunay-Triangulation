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
#include <algorithm>
#include <type_traits>
#include <limits>
#include <math.h>
#include <assert.h>
using namespace std;

#ifdef DEBUG
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

#ifdef __GNUC__
#define UNUSED(x) UNUSED_ ## x __attribute__((__unused__))
#else
#define UNUSED(x) UNUSED_ ## x
#endif

/* Delaunay triangulation O(N log N) */
template<typename Tp = double>
class Delaunay {
public:
	struct point {
		Tp x, y;
		
		inline point (Tp x, Tp y) : x(x), y(y) {};
		inline point () {};
		inline bool operator== (const point & p) const { return x == p.x && y == p.y; }
		inline void operator+= (const point & p) { x+=p.x, y+=p.y; }
		inline void operator-= (const point & p) { x-=p.x, y-=p.y; }
		inline void operator/= (Tp s) { x/=s, y/=s; }
		inline void operator*= (Tp s) { x*=s, y*=s; }
		inline Tp operator() (const point & p) const { Tp xx = x - p.x, yy = y - p.y; return xx*xx + yy*yy; }
		inline Tp operator() () const { return x*x + y*y; }
		inline Tp operator^ (const point & p) const { return x * p.y - y * p.x; }
		inline Tp operator* (const point & p) const { return x * p.x + y * p.y; }
		inline static bool cmp_by_x (const point & p1, const point & p2) { return p1.x < p2.x || (p1.x == p2.x && p1.y < p2.y); }
		inline static bool cmp_by_y (const point & p1, const point & p2) { return p1.y < p2.y || (p1.y == p2.y && p1.x < p2.x); }
		inline bool operator< (const point & p2) const { return x < p2.x || (x == p2.x && y < p2.y); }
	};
	
	struct triangle_basic {
		const point * a, * b, * c;
		
		inline triangle_basic () : a(0),b(0),c(0) {}
		
		inline triangle_basic (const point * a, const point * b, const point * c) : a(a),b(b),c(c) {}
		
		inline static Tp signed_area (const point & p1, const point & p2, const point & p3) {
			return (p2.x - p1.x) * (p3.y - p1.y) - (p2.y - p1.y) * (p3.x - p1.x);
		}
		
		inline static Tp signed_area (const point * p1, const point * p2, const point * p3) {
			return (p2->x - p1->x) * (p3->y - p1->y) - (p2->y - p1->y) * (p3->x - p1->x);
		}
	};
	
	struct triangle_ex;
	struct triangle_fp;
	typedef typename std::conditional<std::is_floating_point<Tp>::value, triangle_fp, triangle_ex>::type triangle;
	
	struct triangle_ex : public triangle_basic {
		union {
			struct {
				triangle * ab, * ac, * bc;
			};
			triangle * edg[3];
		};
		
		inline triangle_ex () : ab(0),ac(0),bc(0) {}
		inline triangle_ex (const point * a, const point * b, const point * c) : triangle_basic(a, b, c),ab(0),ac(0),bc(0) {}
		
		inline void recache () {}
		
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
				return this->c;
			if (ac == t)
				return this->b;
			ASSERT(bc == t);
			return this->a;
		}
		
		inline triangle * get_incident_edge (const triangle * t, const point * p) const {
			if (ab == t)
				return (this->a == p) ? ac : bc;
			if (ac == t)
				return (this->a == p) ? ab : bc;
			return (this->b == p) ? ab : ac;
		}
		
		inline triangle * get_incident_ccw (const point * p) const {
			if (this->a == p)
				return ac;
			if (this->b == p)
				return ab;
			return bc;
		}
		
		inline triangle * get_incident_cw (const point * p) const {
			if (this->a == p)
				return ab;
			if (this->b == p)
				return bc;
			return ac;
		}
		
		inline const point * get_vertex_ccw (const point * p) const {
			if (this->a == p)
				return this->c;
			if (this->b == p)
				return this->a;
			return this->b;
		}
		
		inline const point * get_vertex_cw (const point * p) const {
			if (this->a == p)
				return this->b;
			if (this->b == p)
				return this->c;
			return this->a;
		}
		
		inline triangle * get_edge (const point * p, const point * q) const {
			if ((p == this->a && q == this->b) || (q == this->a && p == this->b))
				return ab;
			if ((p == this->a && q == this->c) || (q == this->a && p == this->c))
				return ac;
			ASSERT((p == this->b && q == this->c) || (q == this->b && p == this->c));
			return bc;
		}
		
		inline size_t get_edge_id (const point * p, const point * q) const {
			if ((p == this->a && q == this->b) || (q == this->a && p == this->b))
				return 0;
			if ((p == this->a && q == this->c) || (q == this->a && p == this->c))
				return 1;
			ASSERT((p == this->b && q == this->c) || (q == this->b && p == this->c));
			return 2;
		}
		
		inline bool has_edge (const triangle_ex * t) const {
			if (ab == t || ac == t || bc == t)
				return true;
			return false;
		}
		
		inline bool check_for_correctness () const {
			return (!ab || ab->has_edge(this)) && (!ac || ac->has_edge(this)) && (!bc || bc->has_edge(this)) && this->signed_area(this->a, this->b, this->c) >= 0;
		}
		
		inline bool degenerate () const { return this->signed_area(* this->a, * this->b, * this->c) == 0; }
		
		inline bool not_in_circumcircle (const point & p, const size_t n) const {
			point p1, p2, p3, p4;
			if (n == 0) {
				p1 = p3 = * this->a, p2 = p4 = * this->b;
				p1 -= * this->c, p2 -= * this->c;
			}
			else if (n == 1) {
				p1 = p3 = * this->c, p2 = p4 = * this->a;
				p1 -= * this->b, p2 -= * this->b;
			}
			else {
				p1 = p3 = * this->b, p2 = p4 = * this->c;
				p1 -= * this->a, p2 -= * this->a;
			}
			p3 -= p, p4 -= p;
			const Tp cosa = p1 * p2, cosb = p3 * p4;
			if (cosa < 0 && cosb < 0)
				return false;
			if (cosa >= 0 && cosb >= 0)
				return true;
			const long double sina = p1 ^ p2, sinb = p3 ^ p4;
			return sina * cosb >= cosa * sinb;
		}
	};
	
	struct triangle_fp : public triangle_ex {
		point circumcentre;
		Tp ccRadSquared;
		
		inline triangle_fp () : triangle_ex() {}
		inline triangle_fp (const point * a, const point * b, const point * c) : triangle_ex(a, b, c) {
			recache();
		}
		
		/* Нужно только если меняются вершины треугольника */
		inline void recache () {
			point bb = * this->b, cc = * this->c;
			bb -= * this->a, cc -= * this->a;
			Tp b2 = bb();
			Tp c2 = cc();
			Tp det = bb ^ cc;
			if (det == 0) { // треугольник вырожденный (все точки на одной прямой)
				circumcentre = point(0, 0);
				ccRadSquared = std::numeric_limits<Tp>::infinity();
			}
			else {
				circumcentre = point(cc.y * b2 - bb.y * c2, bb.x * c2 - cc.x * b2);
				circumcentre /= 2 * det;
				ccRadSquared = circumcentre();
				circumcentre += * this->a;
			}
		}
		
		inline bool degenerate () const { return ccRadSquared == std::numeric_limits<Tp>::infinity(); }
		inline bool not_in_circumcircle (const point & p, const size_t UNUSED(n)) const { return circumcentre(p) * precision() > ccRadSquared; }
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
	vector< pair<edge, triangle *> > merge_queue;
	vector<edge> bad_edges;
	vector< pair<size_t, point> > fixed_points;
	
	static inline constexpr double epsilon () { return 1e-8; }
	static inline constexpr double precision () { return 1.0 + epsilon(); }
	
	inline bool delaunay_cond (const edge & e) const {
		triangle * opposite = e.tri->edg[e.n];
		if (!opposite)
			return true;
		if (e.tri->degenerate() || opposite->degenerate())
			return false;
		const point * op = opposite->get_opposite(e.tri);
		return e.tri->not_in_circumcircle(* op, e.n);
	}
	
	void flip (const edge & e, triangle * res[2]) {
		const triangle_ex top = * e.tri->edg[e.n], bottom = * e.tri; // bottom to right, top to left
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
		res[0] = left, res[1] = right;
	}
	
	bool check_triangulation () const {
		for (size_t i = 0; i < triangles.size(); ++i) {
			const triangle & t = triangles[i];
			ASSERT(t.check_for_correctness());
			for (size_t j = 0; j < points.size(); ++j) {
				const point * p = &points[j];
				if (p == t.a || p == t.b || p == t.c)
					continue;
				if (t.circumcentre(* p) * precision() < t.ccRadSquared)
					return false;
			}
		}
		return true;
	}
	
	triangle * find_rightmost (size_t s, size_t e, const point *& p) {
		triangle * t = 0;
		for (size_t i = s; i < e; ++i) {
			if (triangles[i].ab && triangles[i].ac && triangles[i].bc)
				continue;
			if (t) {
				if (point::cmp_by_x(*p, *triangles[i].a))
					t = &triangles[i], p = t->a;
				if (point::cmp_by_x(*p, *triangles[i].b))
					t = &triangles[i], p = t->b;
				if (point::cmp_by_x(*p, *triangles[i].c))
					t = &triangles[i], p = t->c;
			}
			else {
				t = &triangles[i];
				p = t->a;
				if (point::cmp_by_x(*p, *t->b))
					p = t->b;
				if (point::cmp_by_x(*p, *t->c))
					p = t->c;
			}
		}
		return t;
	}
	
	triangle * find_topmost (size_t s, size_t e, const point *& p) {
		triangle * t = 0;
		for (size_t i = s; i < e; ++i) {
			if (triangles[i].ab && triangles[i].ac && triangles[i].bc)
				continue;
			if (t) {
				if (point::cmp_by_y(*p, *triangles[i].a))
					t = &triangles[i], p = t->a;
				if (point::cmp_by_y(*p, *triangles[i].b))
					t = &triangles[i], p = t->b;
				if (point::cmp_by_y(*p, *triangles[i].c))
					t = &triangles[i], p = t->c;
			}
			else {
				t = &triangles[i];
				p = t->a;
				if (point::cmp_by_y(*p, *t->b))
					p = t->b;
				if (point::cmp_by_y(*p, *t->c))
					p = t->c;
			}
		}
		return t;
	}
	
	triangle * find_leftmost (size_t s, size_t e, const point *& p) {
		triangle * t = 0;
		for (size_t i = s; i < e; ++i) {
			if (triangles[i].ab && triangles[i].ac && triangles[i].bc)
				continue;
			if (t) {
				if (point::cmp_by_x(*triangles[i].a, *p))
					t = &triangles[i], p = t->a;
				if (point::cmp_by_x(*triangles[i].b, *p))
					t = &triangles[i], p = t->b;
				if (point::cmp_by_x(*triangles[i].c, *p))
					t = &triangles[i], p = t->c;
			}
			else {
				t = &triangles[i];
				p = t->a;
				if (point::cmp_by_x(*t->b, *p))
					p = t->b;
				if (point::cmp_by_x(*t->c, *p))
					p = t->c;
			}
		}
		return t;
	}
	
	triangle * find_bottommost (size_t s, size_t e, const point *& p) {
		triangle * t = 0;
		for (size_t i = s; i < e; ++i) {
			if (triangles[i].ab && triangles[i].ac && triangles[i].bc)
				continue;
			if (t) {
				if (point::cmp_by_y(*triangles[i].a, *p))
					t = &triangles[i], p = t->a;
				if (point::cmp_by_y(*triangles[i].b, *p))
					t = &triangles[i], p = t->b;
				if (point::cmp_by_y(*triangles[i].c, *p))
					t = &triangles[i], p = t->c;
			}
			else {
				t = &triangles[i];
				p = t->a;
				if (point::cmp_by_y(*t->b, *p))
					p = t->b;
				if (point::cmp_by_y(*t->c, *p))
					p = t->c;
			}
		}
		return t;
	}
	
	inline static triangle * next_triangle_ccw (triangle * t, const point * p) {
		triangle * nxt = t->get_incident_ccw(p);
		while (nxt)
			t = nxt, nxt = t->get_incident_ccw(p);
		return t;
	}
	
	inline static triangle * next_triangle_cw (triangle * t, const point * p) {
		triangle * nxt = t->get_incident_cw(p);
		while (nxt)
			t = nxt, nxt = t->get_incident_cw(p);
		return t;
	}
	
	inline void connect1 (const point *& p1, const point *& p2, const point *& np1, triangle *& nxt1, triangle *& last) {
		triangles.push_back(triangle(p1, p2, np1));
		triangles.back().ab = last;
		triangles.back().ac = nxt1;
		if (last) {
			last->bc = &triangles.back();
			bad_edges.push_back(edge(last, 2));
		}
		merge_queue.push_back(make_pair(edge(nxt1, nxt1->get_edge_id(p1, np1)), &triangles.back()));
		p1 = np1;
		nxt1 = next_triangle_cw(nxt1, p1);
		np1 = nxt1->get_vertex_cw(p1);
		last = &triangles.back();
	}
	
	inline void connect2 (const point *& p1, const point *& p2, const point *& np2, triangle *& nxt2, triangle *& last) {
		triangles.push_back(triangle(p2, np2, p1));
		triangles.back().ac = last;
		triangles.back().ab = nxt2;
		if (last) {
			last->bc = &triangles.back();
			bad_edges.push_back(edge(last, 2));
		}
		merge_queue.push_back(make_pair(edge(nxt2, nxt2->get_edge_id(p2, np2)), &triangles.back()));
		p2 = np2;
		nxt2 = next_triangle_ccw(nxt2, p2);
		np2 = nxt2->get_vertex_ccw(p2);
		last = &triangles.back();
	}
	
	inline void finish_triangles () {
		while (bad_edges.size()) {
			edge e = bad_edges.back();
			bad_edges.pop_back();
			if (delaunay_cond(e))
				continue;
			triangle * res[2];
			flip(e, res);
			bad_edges.push_back(edge(res[0], 0));
			bad_edges.push_back(edge(res[0], 1));
			bad_edges.push_back(edge(res[1], 1));
			bad_edges.push_back(edge(res[1], 2));
		}
	}
	
	void merge_triangulations (const size_t start, const size_t mid, const size_t end, const bool div_by_x) {
		const point * p1 = 0, * p2 = 0, * np1, * np2;
		triangle * t1 = div_by_x ? find_rightmost(start, mid, p1) : find_topmost(start, mid, p1), * nxt1;
		triangle * t2 = div_by_x ? find_leftmost(mid, end, p2) : find_bottommost(mid, end, p2), * nxt2;
		do {
			for (;; t1 = nxt1, p1 = np1) {
				nxt1 = next_triangle_ccw(t1, p1);
				np1 = nxt1->get_vertex_ccw(p1);
				if (!(triangle::signed_area(p1, p2, np1) < 0))
					break;
			}
			for (;; t2 = nxt2, p2 = np2) {
				nxt2 = next_triangle_cw(t2, p2);
				np2 = nxt2->get_vertex_cw(p2);
				if (!(triangle::signed_area(p1, p2, np2) < 0))
					break;
			}
		} while (triangle::signed_area(p1, p2, np1) < 0);
		// Теперь (p1, p2) - общая касательная
		nxt1 = next_triangle_cw(t1, p1);
		np1 = nxt1->get_vertex_cw(p1);
		nxt2 = next_triangle_ccw(t2, p2);
		np2 = nxt2->get_vertex_ccw(p2);
		for (triangle * last = 0;;) {
			const Tp s1 = triangle::signed_area(p1, p2, np1);
			const Tp s2 = triangle::signed_area(p1, p2, np2);
			if (s1 > 0 && s2 > 0) {
				if (s1 < s2)
					connect1(p1, p2, np1, nxt1, last);
				else
					connect2(p1, p2, np2, nxt2, last);
			}
			else if (s1 > 0)
				connect1(p1, p2, np1, nxt1, last);
			else if (s2 > 0)
				connect2(p1, p2, np2, nxt2, last);
			else
				break;
		}
		while (merge_queue.size()) {
			edge e = merge_queue.back().first;
			triangle * opp = merge_queue.back().second;
			merge_queue.pop_back();
			e.tri->edg[e.n] = opp;
			ASSERT(opp->check_for_correctness());
			ASSERT(e.tri->check_for_correctness());
			bad_edges.push_back(e);
		}
		finish_triangles();
	}
	
	void divide_and_conquer (const size_t start, const size_t end, const bool div_by_x) {
		const size_t n = end - start;
		if (n == 3) {
			const Tp s = triangle::signed_area(points[start], points[start + 1], points[start + 2]);
			if (s > 0)
				triangles.push_back(triangle(&points[start], &points[start + 1], &points[start + 2]));
			else if (s < 0)
				triangles.push_back(triangle(&points[start], &points[start + 2], &points[start + 1]));
			else {
				sort(points.begin() + start, points.begin() + end, point::cmp_by_x);
				triangles.push_back(triangle(&points[start], &points[start + 1], &points[start + 2]));
				triangle & t = triangles.back();
				const Tp dx = t.b->x - t.a->x, dy = t.a->y - t.b->y;
				point shift;
				if (std::abs(dy) > std::abs(dx))
					shift = point(2*epsilon() / dy, 0);
				else
					shift = point(0, 2*epsilon() / dx);
				points[start + 2] += shift;
				fixed_points.push_back(make_pair(start + 2, shift));
				ASSERT(triangle::signed_area(t.a, t.b, t.c) > 0);
			}
			return;
		}
		if (n < 6) { // сливаем 1 точку с n-1
			iter_swap(points.begin() + start, min_element(points.begin() + start, points.begin() + end, div_by_x ? point::cmp_by_x : point::cmp_by_y));
			const size_t ts = triangles.size();
			divide_and_conquer(start + 1, end, !div_by_x);
			const size_t te = triangles.size();
			const point * p1 = &points[start], * p2 = 0, * p3;
			triangle * t2 = div_by_x ? find_leftmost(ts, te, p2) : find_bottommost(ts, te, p2), * t3;
			t3 = next_triangle_cw(t2, p2);
			p3 = t3->get_vertex_cw(p2);
			while (triangle::signed_area(p1, p3, p2) > 0) {
				t2 = t3, p2 = p3;
				t3 = next_triangle_cw(t2, p2);
				p3 = t3->get_vertex_cw(p2);
			}
			t3 = next_triangle_ccw(t2, p2);
			p3 = t3->get_vertex_ccw(p2);
			for (triangle * last = 0; triangle::signed_area(p1, p2, p3) > 0;) {
				triangles.push_back(triangle(p1, p2, p3));
				triangles.back().ab = last;
				triangles.back().bc = t3;
				if (last)
					last->ac = &triangles.back();
				edge e(t3, t3->get_edge_id(p2, p3));
				t3->edg[e.n] = &triangles.back();
				ASSERT(t3->check_for_correctness());
				ASSERT(triangles.back().check_for_correctness());
				bad_edges.push_back(e);
				last = &triangles.back();
				p2 = p3;
				t3 = next_triangle_ccw(t3, p3);
				p3 = t3->get_vertex_ccw(p3);
			}
			finish_triangles();
			return;
		}
		const size_t m = (start + end) / 2;
		nth_element(points.begin() + start, points.begin() + m, points.begin() + end, div_by_x ? point::cmp_by_x : point::cmp_by_y);
		const size_t ts = triangles.size();
		divide_and_conquer(start, m, !div_by_x);
		const size_t tm = triangles.size();
		divide_and_conquer(m, end, !div_by_x);
		const size_t te = triangles.size();
		merge_triangulations(ts, tm, te, div_by_x);
	}
public:
	inline void add_point (Tp x, Tp y) {
		points.push_back(point(x, y));
	}
	
	inline void add_point (const point & p) {
		points.push_back(p);
	}
	
	void build () {
		if (points.size() < 3)
			return;
		triangles.reserve(points.size() * 2); // Euler: V-E+F=2
		random_shuffle(points.begin(), points.end());
		divide_and_conquer(0, points.size(), false);
		for (size_t i = 0; i < fixed_points.size(); ++i)
			points[fixed_points[i].first] -= fixed_points[i].second;
		// TODO: удалять вырожденные треугольники
		fixed_points.clear();
		ASSERT(check_triangulation());
	}
	
	inline vector<triangle> & get_triangles () {
		return triangles;
	}
	
	inline void dump_gnuplot () const {
		for (size_t i = 0; i < triangles.size(); ++i) {
			cout << triangles[i].a->x << '\t' << triangles[i].a->y << endl;
			cout << triangles[i].b->x << '\t' << triangles[i].b->y << endl;
			cout << triangles[i].c->x << '\t' << triangles[i].c->y << endl;
			cout << triangles[i].a->x << '\t' << triangles[i].a->y << endl;
			cout << endl;
		}
	}
};

int main () {
	cin.sync_with_stdio(false);
	cout.sync_with_stdio(false);
	typedef double axis;
	Delaunay<axis> d;
	int n;
	cin>>n;
	for (int i=0;i<n;++i) {
		axis x,y;
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
	/*Delaunay<double> d;
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
	vector< vector<const Delaunay<double>::point *> > cells;
	d.build_voronoi_cells(cells);
	for (size_t i = 0; i < cells.size(); ++i)
		if (cells[i].size())
			answer += cells[i].size(), ++ans;
	cout<<(ans==0 ? 0 : (answer/ans))<<endl;*/
	return 0;
}