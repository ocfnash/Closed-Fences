/*
ID: oliver.1
PROG: fence4
LANG: C++
*/
#include <fstream>
#include <iostream>
#include <vector>

template <typename T>
T det(T a, T b,
      T c, T d)
{
   return a*d - b*c;
}

template <typename T>
T det(T a, T b, T c,
      T d, T e, T f,
      T g, T h, T i)
{
   return a * det(e, f, h, i) -
          b * det(d, f, g, i) +
          c * det(d, e, g, h);
}

class Point
{
public:
   int x, y, z;
   Point(const int x = 0,
         const int y = 0,
         const int z = 1)
   : x(x), y(y), z(z)
   {
   };
};

bool operator==(const Point & p,
                const Point & q)
{
   return det(p.y, p.z, q.y, q.z) == 0 &&
          det(p.x, p.z, q.x, q.z) == 0 &&
          det(p.x, p.y, q.x, q.y) == 0;
}

class Line
{
public:
   Point p, q;
   Line(const Point & p,
        const Point & q)
   : p(p), q(q)
   {
   };
};

typedef Line LineSeg; // I wonder how to do this while retaining type safety?

class ViewPort
{
public:
   Point e;
   LineSeg ls;
   ViewPort(const Point & e,
            const LineSeg & ls)
   : e(e), ls(ls)
   {
   };
};

enum Edge
{
   EdgeA, EdgeB
};

void get_input(std::vector<Point> & endPoints,
               Point& eye)
{
   std::ifstream in("fence4.in");
   int x, y, N;
   in >> N >> eye.x >> eye.y;
   for(int i = 0; i < N; i++)
   {
      in >> x >> y;
      endPoints.push_back(Point(x, y));
   }
   in.close();
   return;
}

void dump_output(std::ofstream& out,
                 const std::vector<Point> & endPoints,
                 const std::vector<bool> & sideVisible)
{
   const std::vector<Point>::size_type N = endPoints.size();

   int n_visible = 0;
   for(std::vector<Point>::size_type i = 0; i < N; i++)
      if(sideVisible[i])
         n_visible++;
   out << n_visible << std::endl;

   for(std::vector<Point>::size_type i = 0; i < N; i++)
   {
      // Very annoying convention for output, hence j etc.
      int j = ((i == N-1) ? N-2 : (i == N-2 ? N-1 : i));
      if(sideVisible[j])
      {
         if(j == N - 1)
         {
            out << endPoints[0].x << " " << endPoints[0].y << " "
                << endPoints[N - 1].x << " " << endPoints[N - 1].y << std::endl;
         }
         else
         {
            out << endPoints[j].x << " " << endPoints[j].y << " "
                << endPoints[j + 1].x << " " << endPoints[j + 1].y << std::endl;
         }
      }
   }
   return;
}

Point intersectLineLine(const Line & l,
                        const Line & m)
{
   const int a = det(l.p.x, l.p.y, l.q.x, l.q.y),
             b = det(l.p.x, l.p.z, l.q.x, l.q.z),
             c = det(m.p.x, m.p.y, m.q.x, m.q.y),
             d = det(m.p.x, m.p.z, m.q.x, m.q.z),
             e = det(l.p.y, l.p.z, l.q.y, l.q.z),
             f = det(m.p.y, m.p.z, m.q.y, m.q.z);
   return Point(det(a, b, c, d),
                det(a, e, c, f),
                det(b, e, d, f));
}

bool pointOnLine(const Point & p,
                 const Line & l)
{
   return 0 == det(p.x, p.y, p.z,
                   l.p.x, l.p.y, l.p.z,
                   l.q.x, l.q.y, l.q.z);
}

bool pointOnLineSeg(const Point & p,
                    const LineSeg & l,
                    const bool strict = false) // strict only used by bad_fence()
{
   if(p.z == 0) return false;

   const int a = det(p.y, p.z, l.p.y, l.p.z),
             b = det(l.q.y, l.q.z, l.p.y, l.p.z),
             c = det(p.x, p.z, l.q.x, l.q.z),
             d = det(l.p.x, l.p.z, l.q.x, l.q.z);

   int top, bottom;
   if(d == 0)
   {
      top = l.q.z * a;
      bottom = p.z * b;
   }
   else
   {
      top = l.p.z * c;
      bottom = p.z * d;
   }

   if(bottom < 0)
   {
      bottom = -bottom;
      top = -top;
   }

   if(!strict)
   {
      return (0 <= top) && (top <= bottom);
   }
   else
   {
      return (0 < top) && (top < bottom);
   }
}

bool lineSegMeetsLine(const LineSeg & ls,
                      const Line & l,
                      const bool strict = false) // strict only used by bad_fence()
{
   if(pointOnLine(ls.p, l) && pointOnLine(ls.q, l))
   {
      // The point of this special case is to avoid intersecting
      // a line with itself in the other case.
      return true; 
   }
   else
   {
      return pointOnLineSeg(intersectLineLine(l, ls), ls, strict);
   }
}

bool lineSegMeetsLineSeg(const LineSeg & l,
                         const LineSeg & m,
                         const bool strict = false) // strict only used by bad_fence()
{
   if(pointOnLine(l.p, m) && pointOnLine(l.q, m))
   {
      return pointOnLineSeg(l.p, m, strict) ||
             pointOnLineSeg(l.q, m, strict) ||
             pointOnLineSeg(m.p, l, strict) ||
             pointOnLineSeg(m.q, l, strict);
   }
   else
   {
      return lineSegMeetsLine(l, m, strict) && lineSegMeetsLine(m, l, strict);
   }
}

int gcd(int a,
        int b)
{
   if(a < 0) a = -a;
   if(b < 0) b = -b;
   if(b == 0)
   {
      return a;
   }
   const int r = a % b;
   return gcd(b, std::min(r, b-r));
}

Point reducePoint(const Point & p)
{
   int d = gcd(p.x, gcd(p.y, p.z));
   if(p.z < 0) d = -d;
   return Point(p.x / d, p.y / d, p.z / d);
}

Point sameSidest(const LineSeg & ls,
                 const Line & l,
                 const Point & r)
{
   const int si = det(ls.p.x, ls.p.y, ls.p.z,
                      l.p.x, l.p.y, l.p.z,
                      l.q.x, l.q.y, l.q.z),
             sj = det(ls.q.x, ls.q.y, ls.q.z,
                      l.p.x, l.p.y, l.p.z,
                      l.q.x, l.q.y, l.q.z),
             sr = det(r.x, r.y, r.z,
                      l.p.x, l.p.y, l.p.z,
                      l.q.x, l.q.y, l.q.z);

   if(sr > 0)
   {
      if(si > sj)
      {
         return ls.p;
      }
      else
      {
         return ls.q;
      }
   }
   else
   {
      if(si < sj)
      {
         return ls.p;
      }
      else
      {
         return ls.q;
      }
   }
}

ViewPort clipEdge(const Edge & edge,
                  const LineSeg & ls,
                  const ViewPort & v)
{
   Point a_(v.ls.p), b_(v.ls.q);
   if(edge != EdgeA)
   {
      a_ = v.ls.q;
      b_ = v.ls.p;
   }
   const Point a__ = reducePoint(intersectLineLine(
                              v.ls,
                              LineSeg(v.e, sameSidest(ls, Line(v.e, a_), b_))));
   if(edge == EdgeA)
   {
      return ViewPort(v.e, LineSeg(a__, b_));
   }
   else
   {
      return ViewPort(v.e, LineSeg(b_, a__));
   }
}

// Tempted to use unique_ptr (or auto_ptr) but unsure USACO compiler supports.
ViewPort * clipByOneSide(const ViewPort & v,
                         const LineSeg & ls)
{
   const Point a(v.ls.p), b(v.ls.q),
               i(ls.p), j(ls.q);
   const bool meetsEA = lineSegMeetsLineSeg(LineSeg(v.e, a), ls),
              meetsEB = lineSegMeetsLineSeg(LineSeg(v.e, b), ls);

   if(meetsEA && meetsEB)
   {
      return NULL;
   }
   else if(!(meetsEA || meetsEB))
   {
      return new ViewPort(v);
   }
   else if(i == a || j == a)
   {
      if(lineSegMeetsLine(Line(b, v.e), ls))
      {
         return new ViewPort(clipEdge(EdgeA, ls, v));
      }
      else
      {
         return new ViewPort(v);
      }
   }
   else if(i == b || j == b)
   {
      if(lineSegMeetsLine(Line(a, v.e), ls))
      {
         return new ViewPort(clipEdge(EdgeB, ls, v));
      }
      else
      {
         return new ViewPort(v);
      }
   }
   else if(meetsEA)
   {
      return new ViewPort(clipEdge(EdgeA, ls, v));
   }
   else // Note meetsEB == true if get here.
   {
      return new ViewPort(clipEdge(EdgeB, ls, v));
   }
}

bool clipByAllSides(const Point & e,
                    const std::vector<Point> & endPoints,
                    const std::vector<Point>::size_type k)
{
   const std::vector<Point>::size_type N = endPoints.size();
   const Point i = endPoints[k],
               j = endPoints[(k+1) % N];

   const int d = det(e.x, e.y, e.z,
                     i.x, i.y, i.z,
                     j.x, j.y, j.z);
   if(d == 0)
   {
      return false;
   }

   ViewPort *nv, v(e, d > 0 ? LineSeg(i, j) : LineSeg(j, i));

   for(std::vector<Point>::size_type n = 1; n < N; n++)
   {
      nv = clipByOneSide(v, LineSeg(endPoints[(n+k) % N], endPoints[(n+k+1) % N]));
      if(!nv)
      {
         return false;
      }
      else
      {
         v = *nv;
         delete nv;
      }
   }
   return true;
}

bool bad_fence(const std::vector<Point> & endPoints)
{
   const std::vector<Point>::size_type N = endPoints.size();
   for(std::vector<Point>::size_type i = 0; i < endPoints.size(); i++)
   {
      for(std::vector<Point>::size_type j = 0; j < endPoints.size(); j++)
      {
         if(i == j)
         {
            continue;
         }
         if(endPoints[i] == endPoints[j])
         {
            return true;
         }
         if(lineSegMeetsLineSeg(LineSeg(endPoints[i], endPoints[(i+1) % N]),
                                LineSeg(endPoints[j], endPoints[(j+1) % N]),
                                true))
         {
            return true;
         }
      }
   }
   return false;
}

int main(void)
{
   std::vector<Point> endPoints;
   Point eye;

   get_input(endPoints, eye);

   std::ofstream out("fence4.out");
   if(bad_fence(endPoints))
   {
      out << "NOFENCE" << std::endl;
      out.close();
      return 0;
   }

   std::vector<bool> sideVisible;
   for(std::vector<Point>::size_type k = 0; k < endPoints.size(); k++)
   {
      sideVisible.push_back(clipByAllSides(eye, endPoints, k));
   }

   dump_output(out, endPoints, sideVisible);
   out.close();

   // To aid comparison with Haskell output:
   std::cout << "[";
   for(std::vector<bool>::size_type k = 0; k < sideVisible.size(); k++)
   {
      std::cout << (sideVisible[k] ? "True" : "False");
      if(k < sideVisible.size()-1)
         std::cout << ",";
   }
   std::cout << "]" << std::endl;
   return 0;
}
