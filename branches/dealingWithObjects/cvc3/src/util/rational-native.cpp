/*****************************************************************************/
/*!
 * \file rational-native.cpp
 *
 * \brief Implementation of class Rational using native (bounded
 * precision) computer arithmetic
 *
 * Author: Sergey Berezin
 *
 * Created: Mon Jul 28 12:18:03 2003
 *
 * <hr>
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 *
 * <hr>
 *
 */
/*****************************************************************************/

#ifdef RATIONAL_NATIVE

#include "compat_hash_set.h"
#include "rational.h"
// For atol() (ASCII to long)
#include <stdlib.h>
#include <limits.h>
#include <errno.h>
#include <sstream>
#include <math.h>

#define OVERFLOW_MSG "\nThis is NOT a bug, but an explicit feature to preserve soundness\nwhen CVC3 uses native computer arithmetic (finite precision).  To\navoid these types of errors, please recompile CVC3 with GMP library."

namespace CVC3 {

  using namespace std;

  //! Add two integers and check for overflows
  static long int plus(long int x, long int y) {
    long int res = x+y;
    FatalAssert(((x > 0) != (y > 0)) || ((x > 0) == (res > 0)),
                "plus(x,y): arithmetic overflow" OVERFLOW_MSG);
    return res;
  }

  //! Add two integers and check for overflows
  static unsigned long uplus(unsigned long x, unsigned long y) {
    unsigned long res = x+y;
    FatalAssert(res >= x && res >= y,
                "uplus(x,y): arithmetic overflow" OVERFLOW_MSG);
    return res;
  }

  //! Subtract two unsigned integers and check for overflows
  static unsigned long unsigned_minus(unsigned long x, unsigned long y) {
    unsigned long res = x-y;
    FatalAssert(res <= x,
                "unsigned_minus(x,y): arithmetic overflow" OVERFLOW_MSG);
    return res;
  }

  //! Multiply two unsigned integers and check for overflows
  static unsigned long umult(unsigned long x, unsigned long y) {
    unsigned long res = x*y;
    FatalAssert(res == 0 || res/x == y,
                "umult(x,y): arithmetic overflow" OVERFLOW_MSG);
    return res;
  }

  //! Shift two unsigned integers and check for overflow
  static unsigned long ushift(unsigned long x, unsigned y) {
    FatalAssert(y < (unsigned)numeric_limits<unsigned long>::digits,
                "ushift(x,y): arithmetic overflow" OVERFLOW_MSG);
    unsigned long res = (x << y);
    FatalAssert((res >> y) == x,
                "ushift(x,y): arithmetic overflow" OVERFLOW_MSG);
    return res;
  }

  //! Compute GCD using Euclid's algorithm (from Aaron Stump's code)
  static unsigned long ugcd(unsigned long n1, unsigned long n2) {
    DebugAssert(n1!=0 && n2!=0,
		"gcd("+int2string(n1)+", "+int2string(n2)+"): bad args");
  if (n1 < n2) {
    long int tmp = n1;
    n1 = n2;
    n2 = tmp;
  }

  // at this point, n1 >= n2
  long int r = n1 % n2;
  if (!r)
    return n2;

  return ugcd(n2, r);
}

  //! Unary minus which checks for overflows
  static long int uminus(long int x) {
    FatalAssert(x == 0 || x != -x, "uminus(x): arithmetic overflow"
                OVERFLOW_MSG);
    return -x;
  }

  //! Multiply two integers and check for overflows
  static long int mult(long int x, long int y) {
    long int res = x*y;
    FatalAssert(x==0 || res/x == y, "mult(x,y): arithmetic overflow"
                OVERFLOW_MSG);
    return res;
  }

  //! Compute GCD using Euclid's algorithm (from Aaron Stump's code)
  static long int gcd(long int n1, long int n2) {
    DebugAssert(n1!=0 && n2!=0,
		"gcd("+int2string(n1)+", "+int2string(n2)+"): bad args");
  // First, make the arguments positive
  if(n1 < 0) n1 = uminus(n1);
  if(n2 < 0) n2 = uminus(n2);

  if (n1 < n2) {
    long int tmp = n1;
    n1 = n2;
    n2 = tmp;
  }

  // at this point, n1 >= n2
  long int r = n1 % n2;
  if (!r)
    return n2;

  return gcd(n2, r);
}

  //! Compute LCM
  static long int lcm(long int n1, long int n2) {
    long int g = gcd(n1,n2);
    return mult(n1/g, n2);
  }

  static long int ulcm(unsigned long n1, unsigned long n2) {
    long int g = ugcd(n1,n2);
    return umult(n1/g, n2);
  }

  // Implementation of the forward-declared internal class
  class Rational::Impl {
    long int d_num; //!< Numerator
    long int d_denom; //!< Denominator
    //! Make the rational number canonical
    void canonicalize();
  public:
    //! Default Constructor
    Impl(): d_num(0), d_denom(1) { }
    //! Copy constructor
    Impl(const Impl &x) : d_num(x.d_num), d_denom(x.d_denom) { }
    //! Constructor from unsigned long
    Impl(unsigned long n) :d_num(n), d_denom(1) {
      FatalAssert(d_num >= 0, "Rational::Impl(unsigned long) - arithmetic overflow");
    }
    //! Constructor from a pair of integers
    Impl(long int n, long int d): d_num(n), d_denom(d) { canonicalize(); }
    //! Constructor from a string
    Impl(const string &n, int base);
    //! Constructor from a pair of strings
    Impl(const string &n, const string& d, int base);
    // Destructor
    virtual ~Impl() { }
    //! Get numerator
    long int getNum() const { return d_num; }
    //! Get denominator
    long int getDen() const { return d_denom; }

    //! Unary minus
    Impl operator-() const;

    //! Equality
    friend bool operator==(const Impl& x, const Impl& y) {
      return (x.d_num == y.d_num && x.d_denom == y.d_denom);
    }
    //! Dis-equality
    friend bool operator!=(const Impl& x, const Impl& y) {
      return (x.d_num != y.d_num || x.d_denom != y.d_denom);
    }
    /*!
     * Compare x=n1/d1 and y=n2/d2 as n1*f2 < n2*f1, where f1=d1/f,
     * f2=d2/f, and f=lcm(d1,d2)
     */
    friend bool operator<(const Impl& x, const Impl& y) {
      Impl diff(x-y);
      return diff.d_num < 0;
    }

    friend bool operator<=(const Impl& x, const Impl& y) {
      return (x == y || x < y);
    }

    friend bool operator>(const Impl& x, const Impl& y) {
      Impl diff(x-y);
      return diff.d_num > 0;
    }

    friend bool operator>=(const Impl& x, const Impl& y) {
      return (x == y || x > y);
    }

    /*! Addition of x=n1/d1 and y=n2/d2: n1*g2 + n2*g1, where g1=d1/g,
     * g2=d2/g, and g=lcm(d1,d2)
     */
    friend Impl operator+(const Impl& x, const Impl& y) {
      long int d1(x.getDen()), d2(y.getDen());
      long int f(lcm(d1,d2)), f1(f/d1), f2(f/d2);
      long int n = plus(mult(x.getNum(), f1),  mult(y.getNum(), f2));
      return Impl(n, f);
    }

    friend Impl operator-(const Impl& x, const Impl& y) {
      TRACE("rational", "operator-(", x, ", "+y.toString()+")");
      long int d1(x.getDen()), d2(y.getDen());
      long int f(lcm(d1,d2)), f1(f/d1), f2(f/d2);
      long int n = plus(mult(x.getNum(), f1),  uminus(mult(y.getNum(), f2)));
      Impl res(n, f);
      TRACE("rational", "  => ", res, "");
      return res;
    }

    /*!
     * Multiplication of x=n1/d1, y=n2/d2:
     * (n1/g1)*(n2/g2)/(d1/g2)*(d2/g1), where g1=gcd(n1,d2) and
     * g2=gcd(n2,d1)
     */
    friend Impl operator*(const Impl& x, const Impl& y) {
      long int n1(x.getNum()), d1(x.getDen()), n2(y.getNum()), d2(y.getDen());
      long int g1(n1? gcd(n1,d2) : 1), g2(n2? gcd(n2,d1) : 1);
      long int n(mult(n1/g1, n2/g2)), d(mult(d1/g2, d2/g1));
      return Impl(n,d);
    }

    /*!
     * Division of x=n1/d1, y=n2/d2:
     * (n1/g1)*(d2/g2)/(d1/g2)*(n2/g1), where g1=gcd(n1,n2) and
     * g2=gcd(d1,d2)
     */
    friend Impl operator/(const Impl& x, const Impl& y) {
      long int n1(x.getNum()), d1(x.getDen()), n2(y.getNum()), d2(y.getDen());
      DebugAssert(n2 != 0, "Impl::operator/: divisor is 0");
      long int g1(n1? gcd(n1,n2) : 1), g2(gcd(d1,d2));
      long int n(n1? mult(n1/g1, d2/g2) : 0), d(n1? mult(d1/g2, n2/g1) : 1);
      return Impl(n,d);
    }

    friend Impl operator%(const Impl& x, const Impl& y) {
      DebugAssert(x.getDen() == 1 && y.getDen() == 1,
		  "Impl % Impl: x and y must be integers");
      return Impl(x.getNum() % y.getNum(), 1);
    }

    //! Print to string
    string toString(int base = 10) const {
      ostringstream ss;
      if (d_num == 0) ss << "0";
      else if (base == 10) {
        ss << d_num;
        if (d_denom != 1)
          ss << "/" << d_denom;
      }
      else {
        vector<int> vec;
        long num = d_num;
        while (num) {
          vec.push_back(num % base);
          num = num / base;
        }
        while (!vec.empty()) {
          if (base > 10 && vec.back() > 10) {
            ss << (char)('A' + (vec.back()-10));
          }
          else ss << vec.back();
          vec.pop_back();
        }
        if(d_denom != 1) {
          ss << "/";
          if (d_denom == 0) ss << "0";
          else {
            num = d_denom;
            while (num) {
              vec.push_back(num % base);
              num = num / base;
            }
            while (!vec.empty()) {
              if (base > 10 && vec.back() > 10) {
                ss << (char)('A' + (vec.back()-10));
              }
              else ss << vec.back();
              vec.pop_back();
            }
          }
        }
      }
      return(ss.str());
    }

    //! Printing to ostream
    friend ostream& operator<<(ostream& os, const Rational::Impl& n) {
      return os << n.toString();
    }

  };

  // Make the rational number canonical
  void Rational::Impl::canonicalize() {
    DebugAssert(d_denom != 0,
                "Rational::Impl::canonicalize: bad denominator: "
                +int2string(d_denom));
    if(d_num == 0) {
      d_denom = 1;
    } else {
      if(d_denom < 0) {
	d_num = uminus(d_num);
	d_denom = uminus(d_denom);
      }
      long int d = gcd(d_num, d_denom);
      if(d != 1) {
	d_num /= d;
	d_denom /= d;
      }
    }
  }

  // Constructor from a string
  Rational::Impl::Impl(const string &n, int base) {
    size_t i, iend;
    for(i=0,iend=n.size(); i<iend && n[i] != '/'; ++i);
    if(i<iend)
      // Found slash at i
      *this = Impl(n.substr(0,i-1), n.substr(i+1,iend-1), base);
    else
      *this = Impl(n, "1", base);
    canonicalize();
  }
  // Constructor from a pair of strings
  Rational::Impl::Impl(const string &n, const string& d, int base) {
    d_num = strtol(n.c_str(), NULL, base);
    FatalAssert(d_num != LONG_MIN &&  d_num != LONG_MAX,
                "Rational::Impl(string, string): arithmetic overflow:"
                "n = "+n+", d="+d+", base="+int2string(base)
                +OVERFLOW_MSG);
    d_denom = strtol(d.c_str(), NULL, base);
    FatalAssert(d_denom != LONG_MIN &&  d_denom != LONG_MAX,
                "Rational::Impl(string, string): arithmetic overflow:"
                "n = "+n+", d="+d+", base="+int2string(base)
                +OVERFLOW_MSG);
    canonicalize();
  }

  Rational::Impl Rational::Impl::operator-() const {
    return Impl(uminus(d_num), d_denom);
  }


  //! Default constructor
  Rational::Rational() : d_n(new Impl) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  //! Copy constructor
  Rational::Rational(const Rational &n) : d_n(new Impl(*n.d_n)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }

  Rational::Rational(const Unsigned &n) : d_n(new Impl(n.getUnsigned())) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }

  //! Private constructor
  Rational::Rational(const Impl& t): d_n(new Impl(t)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  Rational::Rational(int n, int d): d_n(new Impl(n, d)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  // Constructors from strings
  Rational::Rational(const char* n, int base)
    : d_n(new Impl(string(n), base)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  Rational::Rational(const string& n, int base)
    : d_n(new Impl(n, base)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  Rational::Rational(const char* n, const char* d, int base)
    : d_n(new Impl(string(n), string(d), base)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  Rational::Rational(const string& n, const string& d, int base)
    : d_n(new Impl(n, d, base)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
  // Destructor
  Rational::~Rational() {
    delete d_n;
#ifdef _DEBUG_RATIONAL_
    int &num_deleted = getDeleted();
    num_deleted++;
    printStats();
#endif
  }

  // Get components
  Rational Rational::getNumerator() const
    { return Rational(Impl(d_n->getNum(), 1)); }
  Rational Rational::getDenominator() const
    { return Rational(Impl(d_n->getDen(), 1)); }

  bool Rational::isInteger() const { return 1 == d_n->getDen(); }

  // Assignment
  Rational& Rational::operator=(const Rational& n) {
    if(this == &n) return *this;
    delete d_n;
    d_n = new Impl(*n.d_n);
    return *this;
  }

  ostream &operator<<(ostream &os, const Rational &n) {
    return(os << n.toString());
  }


  // Check that argument is an int and print an error message otherwise

  static void checkInt(const Rational& n, const string& funName) {
    DebugAssert(n.isInteger(),
		("CVC3::Rational::" + funName
		 + ": argument is not an integer: " + n.toString()).c_str());
  }

    /* Computes gcd and lcm on *integer* values. Result is always a
       positive integer.  In this implementation, it is guaranteed by
       GMP. */

  Rational gcd(const Rational &x, const Rational &y) {
    checkInt(x, "gcd(*x*,y)");
    checkInt(y, "gcd(x,*y*)");
    return Rational(Rational::Impl(gcd(x.d_n->getNum(), y.d_n->getNum()), 1));
  }

  Rational gcd(const vector<Rational> &v) {
    long int g(1);
    if(v.size() > 0) {
      checkInt(v[0], "gcd(vector<Rational>[0])");
      g = v[0].d_n->getNum();
    }
    for(size_t i=1; i<v.size(); i++) {
      checkInt(v[i], "gcd(vector<Rational>)");
      if(g == 0) g = v[i].d_n->getNum();
      else if(v[i].d_n->getNum() != 0)
	g = gcd(g, v[i].d_n->getNum());
    }
    return Rational(Rational::Impl(g,1));
  }

  Rational lcm(const Rational &x, const Rational &y) {
    long int g;
    checkInt(x, "lcm(*x*,y)");
    checkInt(y, "lcm(x,*y*)");
    g = lcm(x.d_n->getNum(), y.d_n->getNum());
    return Rational(Rational::Impl(g, 1));
  }

  Rational lcm(const vector<Rational> &v) {
    long int g(1);
    for(size_t i=0; i<v.size(); i++) {
      checkInt(v[i], "lcm(vector<Rational>)");
      if(v[i].d_n->getNum() != 0)
	g = lcm(g, v[i].d_n->getNum());
    }
    return Rational(Rational::Impl(g,1));
  }

  Rational abs(const Rational &x) {
    long int n(x.d_n->getNum());
    if(n>=0) return x;
    return Rational(Rational::Impl(-n, x.d_n->getDen()));
  }

  Rational floor(const Rational &x) {
    if(x.d_n->getDen() == 1) return x;
    long int n = x.d_n->getNum();
    long int nAbs = (n<0)? uminus(n) : n;
    long int q = nAbs / x.d_n->getDen();
    if(n < 0) q = plus(uminus(q), -1);
    return Rational(Rational::Impl(q,1));
  }

  Rational ceil(const Rational &x) {
    if(x.d_n->getDen() == 1) return x;
    long int n = x.d_n->getNum();
    long int nAbs = (n<0)? -n : n;
    long int q = nAbs / x.d_n->getDen();
    if(n > 0) q = plus(q, 1);
    else q = uminus(q);
    return Rational(Rational::Impl(q,1));
  }

  Rational mod(const Rational &x, const Rational &y) {
    checkInt(x, "mod(*x*,y)");
    checkInt(y, "mod(x,*y*)");
    long int r = x.d_n->getNum() % y.d_n->getNum();
    return(Rational(Rational::Impl(r,1)));
  }

  Rational intRoot(const Rational& base, unsigned long int n) {
    checkInt(base, "intRoot(*x*,y)");
    checkInt(n, "intRoot(x,*y*)");
    double b = base.d_n->getNum();
    double root = n;
    root = 1/root;
    b = ::pow(b, root);
    long res = (long) ::floor(b);
    if (::pow((long double)res, (int)n) == base.d_n->getNum()) {
      return Rational(Rational::Impl(res,1));
    }
    return Rational(Rational::Impl((long)0,(long)1));
  }

  string Rational::toString(int base) const {
    return(d_n->toString(base));
  }

  size_t Rational::hash() const {
    std::hash<const char *> h;
    return h(toString().c_str());
  }

  void Rational::print() const {
    cout << (*this) << endl;
  }

  // Unary minus
  Rational Rational::operator-() const {
    return Rational(Rational::Impl(-(d_n->getNum()), d_n->getDen()));
  }

  Rational &Rational::operator+=(const Rational &n2) {
    *this = (*this) + n2;
    return *this;
  }

  Rational &Rational::operator-=(const Rational &n2) {
    *this = (*this) - n2;
    return *this;
  }

  Rational &Rational::operator*=(const Rational &n2) {
    *this = (*this) * n2;
    return *this;
  }

  Rational &Rational::operator/=(const Rational &n2) {
    *this = (*this) / n2;
    return *this;
  }

  int Rational::getInt() const {
    checkInt(*this, "getInt()");
    long int res = d_n->getNum();
    FatalAssert(res >= INT_MIN && res <= INT_MAX,
                "Rational::getInt(): arithmetic overflow on "+toString() +
                OVERFLOW_MSG);
    return (int)res;
  }

  unsigned int Rational::getUnsigned() const {
    checkInt(*this, "getUnsigned()");
    long int res = d_n->getNum();
    FatalAssert(res >= 0 && res <= (long int)UINT_MAX,
                "Rational::getUnsigned(): arithmetic overflow on " + toString() +
		OVERFLOW_MSG);
    return (unsigned int)res;
  }

#ifdef _DEBUG_RATIONAL_
  void Rational::printStats() {
      int &num_created = getCreated();
      int &num_deleted = getDeleted();
      if(num_created % 1000 == 0 || num_deleted % 1000 == 0) {
	std::cerr << "Rational(" << *d_n << "): created " << num_created
		  << ", deleted " << num_deleted
		  << ", currently alive " << num_created-num_deleted
		  << std::endl;
      }
    }
#endif

    bool operator==(const Rational &n1, const Rational &n2) {
      return(*n1.d_n == *n2.d_n);
    }

    bool operator<(const Rational &n1, const Rational &n2) {
      return(*n1.d_n < *n2.d_n);
    }

    bool operator<=(const Rational &n1, const Rational &n2) {
      return(*n1.d_n <= *n2.d_n);
    }

    bool operator>(const Rational &n1, const Rational &n2) {
      return(*n1.d_n > *n2.d_n);
    }

    bool operator>=(const Rational &n1, const Rational &n2) {
      return(*n1.d_n >= *n2.d_n);
    }

    bool operator!=(const Rational &n1, const Rational &n2) {
      return(*n1.d_n != *n2.d_n);
    }

    Rational operator+(const Rational &n1, const Rational &n2) {
      return Rational(Rational::Impl(*n1.d_n + *n2.d_n));
    }

    Rational operator-(const Rational &n1, const Rational &n2) {
      return Rational(Rational::Impl((*n1.d_n) - (*n2.d_n)));
    }

    Rational operator*(const Rational &n1, const Rational &n2) {
      return Rational(Rational::Impl((*n1.d_n) * (*n2.d_n)));
    }

    Rational operator/(const Rational &n1, const Rational &n2) {
      return Rational(Rational::Impl(*n1.d_n / *n2.d_n));
    }

    Rational operator%(const Rational &n1, const Rational &n2) {
      return Rational(Rational::Impl(*n1.d_n % *n2.d_n));
    }

  // Implementation of the forward-declared internal class
  class Unsigned::Impl {
    unsigned long d_num;
  public:
    //! Default Constructor
    Impl(): d_num(0) { }
    //! Copy constructor
    Impl(const Impl &x) : d_num(x.d_num) { }
    //! Constructor from an unsigned integer
    Impl(unsigned long n): d_num(n) { }
    //! Constructor from an int
    Impl(int n): d_num(n) {
      FatalAssert(n >= 0, "Attempt to create Unsigned from negative integer");
    }

    //! Constructor from a string
    Impl(const string &n, int base);
    // Destructor
    virtual ~Impl() { }
    //! Get unsigned
    unsigned long getUnsigned() const { return d_num; }


    //! Equality
    friend bool operator==(const Impl& x, const Impl& y) {
      return (x.d_num == y.d_num);
    }
    //! Dis-equality
    friend bool operator!=(const Impl& x, const Impl& y) {
      return (x.d_num != y.d_num);
    }
    friend bool operator<(const Impl& x, const Impl& y) {
      return x.d_num < y.d_num;
    }

    friend bool operator<=(const Impl& x, const Impl& y) {
      return (x.d_num <= y.d_num);
    }

    friend bool operator>(const Impl& x, const Impl& y) {
      return x.d_num > y.d_num;
    }

    friend bool operator>=(const Impl& x, const Impl& y) {
      return x.d_num >= y.d_num;
    }

    friend Impl operator+(const Impl& x, const Impl& y) {
      return Impl(uplus(x.d_num, y.d_num));
    }

    friend Impl operator-(const Impl& x, const Impl& y) {
      unsigned long n = unsigned_minus(x.d_num, y.d_num);
      Impl res(n);
      return res;
    }

    friend Impl operator*(const Impl& x, const Impl& y) {
      unsigned long n(umult(x.d_num, y.d_num));
      return Impl(n);
    }

    friend Impl operator/(const Impl& x, const Impl& y) {
      DebugAssert(y.d_num != 0, "Impl::operator/: divisor is 0");
      unsigned long n(x.d_num / y.d_num);
      return Impl(n);
    }

    friend Impl operator%(const Impl& x, const Impl& y) {
      DebugAssert(y.d_num != 0,
		  "Impl % Impl: y must be non-zero");
      return Impl(x.d_num % y.d_num);
    }

    friend Impl operator<<(const Impl& x, unsigned y) {
      unsigned long n(ushift(x.d_num, y));
      return Impl(n);
    }

    friend Impl operator&(const Impl& x, const Impl& y) {
      return Impl(x.d_num & y.d_num);
    }

    //! Print to string
    string toString(int base = 10) const {
      ostringstream ss;
      if (d_num == 0) ss << "0";
      else if (base == 10) {
        ss << d_num;
      }
      else {
        vector<int> vec;
        long num = d_num;
        while (num) {
          vec.push_back(num % base);
          num = num / base;
        }
        while (!vec.empty()) {
          if (base > 10 && vec.back() > 10) {
            ss << (char)('A' + (vec.back()-10));
          }
          else ss << vec.back();
          vec.pop_back();
        }
      }
      return(ss.str());
    }

    //! Printing to ostream
    friend ostream& operator<<(ostream& os, const Unsigned::Impl& n) {
      return os << n.toString();
    }

  };

  // Constructor from a pair of strings
  Unsigned::Impl::Impl(const string &n, int base) {
    d_num = strtoul(n.c_str(), NULL, base);
    FatalAssert(d_num != ULONG_MAX,
                "Unsigned::Impl(string): arithmetic overflow:"
                "n = "+n+", base="+int2string(base)
                +OVERFLOW_MSG);
  }

  //! Default constructor
  Unsigned::Unsigned() : d_n(new Impl) { }
  //! Copy constructor
  Unsigned::Unsigned(const Unsigned &n) : d_n(new Impl(*n.d_n)) { }

  //! Private constructor
  Unsigned::Unsigned(const Impl& t): d_n(new Impl(t)) { }

  Unsigned::Unsigned(unsigned n): d_n(new Impl((unsigned long)n)) { }
  Unsigned::Unsigned(int n): d_n(new Impl(n)) { }

  // Constructors from strings
  Unsigned::Unsigned(const char* n, int base)
    : d_n(new Impl(string(n), base)) { }
  Unsigned::Unsigned(const string& n, int base)
    : d_n(new Impl(n, base)) { }

  // Destructor
  Unsigned::~Unsigned() {
    delete d_n;
  }

  // Assignment
  Unsigned& Unsigned::operator=(const Unsigned& n) {
    if(this == &n) return *this;
    delete d_n;
    d_n = new Impl(*n.d_n);
    return *this;
  }

  ostream &operator<<(ostream &os, const Unsigned &n) {
    return(os << n.toString());
  }

  Unsigned gcd(const Unsigned &x, const Unsigned &y) {
    return Unsigned(Unsigned::Impl(ugcd(x.d_n->getUnsigned(), y.d_n->getUnsigned())));
  }

  Unsigned gcd(const vector<Unsigned> &v) {
    unsigned long g(1);
    if(v.size() > 0) {
      g = v[0].d_n->getUnsigned();
    }
    for(size_t i=1; i<v.size(); i++) {
      if(g == 0) g = v[i].d_n->getUnsigned();
      else if(v[i].d_n->getUnsigned() != 0)
	g = ugcd(g, v[i].d_n->getUnsigned());
    }
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned lcm(const Unsigned &x, const Unsigned &y) {
    unsigned long g;
    g = ulcm(x.d_n->getUnsigned(), y.d_n->getUnsigned());
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned lcm(const vector<Unsigned> &v) {
    unsigned long g(1);
    for(size_t i=0; i<v.size(); i++) {
      if(v[i].d_n->getUnsigned() != 0)
	g = ulcm(g, v[i].d_n->getUnsigned());
    }
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned mod(const Unsigned &x, const Unsigned &y) {
    unsigned long r = x.d_n->getUnsigned() % y.d_n->getUnsigned();
    return(Unsigned(Unsigned::Impl(r)));
  }

  Unsigned intRoot(const Unsigned& base, unsigned long int n) {
    double b = base.d_n->getUnsigned();
    double root = n;
    root = 1/root;
    b = ::pow(b, root);
    unsigned long res = (unsigned long) ::floor(b);
    if (::pow((long double)res, (int)n) == base.d_n->getUnsigned()) {
      return Unsigned(Unsigned::Impl(res));
    }
    return Unsigned(Unsigned::Impl((unsigned long)0));
  }

  string Unsigned::toString(int base) const {
    return(d_n->toString(base));
  }

  size_t Unsigned::hash() const {
    std::hash<const char *> h;
    return h(toString().c_str());
  }

  void Unsigned::print() const {
    cout << (*this) << endl;
  }

  Unsigned &Unsigned::operator+=(const Unsigned &n2) {
    *this = (*this) + n2;
    return *this;
  }

  Unsigned &Unsigned::operator-=(const Unsigned &n2) {
    *this = (*this) - n2;
    return *this;
  }

  Unsigned &Unsigned::operator*=(const Unsigned &n2) {
    *this = (*this) * n2;
    return *this;
  }

  Unsigned &Unsigned::operator/=(const Unsigned &n2) {
    *this = (*this) / n2;
    return *this;
  }

  unsigned long Unsigned::getUnsigned() const {
    return d_n->getUnsigned();
  }

  bool operator==(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n == *n2.d_n);
  }

  bool operator<(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n < *n2.d_n);
  }

  bool operator<=(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n <= *n2.d_n);
  }

  bool operator>(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n > *n2.d_n);
  }

  bool operator>=(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n >= *n2.d_n);
  }

  bool operator!=(const Unsigned &n1, const Unsigned &n2) {
    return(*n1.d_n != *n2.d_n);
  }

  Unsigned operator+(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned(Unsigned::Impl(*n1.d_n + *n2.d_n));
  }

  Unsigned operator-(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned(Unsigned::Impl((*n1.d_n) - (*n2.d_n)));
  }

  Unsigned operator*(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned(Unsigned::Impl((*n1.d_n) * (*n2.d_n)));
  }

  Unsigned operator/(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned(Unsigned::Impl(*n1.d_n / *n2.d_n));
  }

  Unsigned operator%(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned(Unsigned::Impl(*n1.d_n % *n2.d_n));
  }

  Unsigned operator<<(const Unsigned& n1, unsigned n2) {
    return Unsigned(Unsigned::Impl(*n1.d_n << n2));
  }

  Unsigned operator&(const Unsigned& n1, const Unsigned& n2) {
    return Unsigned(Unsigned::Impl(*n1.d_n & *n2.d_n));
  }

  Unsigned Rational::getUnsignedMP() const {
    checkInt(*this, "getUnsignedMP()");
    long int res = d_n->getNum();
    FatalAssert(res >= 0 && res <= (long int)UINT_MAX,
                "Rational::getUnsignedMP(): arithmetic overflow on " + toString() +
		OVERFLOW_MSG);
    return Unsigned((unsigned int)res);
  }


} /* close namespace */

#endif
