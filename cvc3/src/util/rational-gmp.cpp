/*****************************************************************************/
/*!
 * \file rational-gmp.cpp
 *
 * \brief Implementation of class Rational using GMP library (C interface)
 *
 * Author: Sergey Berezin
 *
 * Created: Mon Aug  4 10:06:04 2003
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

#ifdef RATIONAL_GMP

#include "compat_hash_set.h"
#include "rational.h"

#include <climits>
#include <sstream>
#include <gmp.h>
#include <limits.h>

namespace CVC3 {

  using namespace std;

  //! Implementation of the forward-declared internal class
  class Rational::Impl {
    mpq_t d_n;
    //! Make the rational number canonical
    void canonicalize() { mpq_canonicalize(d_n); }
  public:
    //! Default Constructor
    Impl() { mpq_init(d_n); }
    //! Copy constructor (assumes x is canonicalized)
    Impl(const Impl &x) { mpq_init(d_n); mpq_set(d_n, x.d_n); }
    //! Constructor from mpq_t
    Impl(mpq_t n) {
      mpq_init(d_n);
      mpq_set(d_n, n);
      canonicalize();
    }
    //! Constructor from a pair of mpz_t (integers)
    Impl(mpz_t n, mpz_t d) {
      mpq_init(d_n);
      mpq_set_num(d_n, n); mpq_set_den(d_n, d);
      canonicalize();
    }
    //! Constructor from a single mpz_t (integer)
    Impl(mpz_t n) {
      mpq_init(d_n);
      mpq_set_num(d_n, n);
      canonicalize();
    }
    //! Constructor from a pair of integers
    Impl(long int n, long int d);
    //! Constructor from a pair of unsigned integers
    Impl(unsigned int n, unsigned int d, unsigned int /* dummy arg */);
    //! Constructor from a string
    Impl(const string &n, int base);
    //! Constructor from a pair of strings
    Impl(const string &n, const string& d, int base);
    // Destructor
    virtual ~Impl() { mpq_clear(d_n); }

    //! Assignment
    Impl& operator=(const Impl& x) {
      if(this == &x) return *this;
      mpq_set(d_n, x.d_n);
      return *this;
    }

    //! Get numerator
    Impl getNum() const {
      return Impl(mpq_numref(const_cast<Impl*>(this)->d_n));
    }
    //! Get denominator
    Impl getDen() const {
      return Impl(mpq_denref(const_cast<Impl*>(this)->d_n));
    }

    int getInt() const {
      // Check for overflow
      static Impl min((int)INT_MIN, 1), max((int)INT_MAX, 1);
      FatalAssert(isInteger() && min <= *this && *this <= max,
                  "Rational::getInt(): Arithmetic overflow for "
                  +toString());
      return mpz_get_si(mpq_numref(d_n));
    }

     unsigned int getUnsigned() const {
      // Check for overflow
      static Impl min(0, 1, 0), max(UINT_MAX, 1, 0);
      FatalAssert(min <= *this && *this <= max,
                  "Rational::getUnsigned(): Arithmetic overflow for "
                  +toString());
      return mpz_get_ui(mpq_numref(d_n));
    }

    Unsigned getUnsignedMP() const;

    //! Unary minus
    Impl operator-() const;
    //! Get the floor
    Impl floor() const;
    //! Get the ceiling
    Impl ceil() const;

    //! Testing whether the denominator is 1
    bool isInteger() const;

    //! Equality
    friend bool operator==(const Impl& x, const Impl& y) {
      return mpq_equal(x.d_n, y.d_n);
    }

    //! Dis-equality
    friend bool operator!=(const Impl& x, const Impl& y) {
      return !mpq_equal(x.d_n, y.d_n);
    }
    //! Less than
    friend bool operator<(const Impl& x, const Impl& y) {
      return mpq_cmp(x.d_n, y.d_n) < 0;
    }

    friend bool operator<=(const Impl& x, const Impl& y) {
      return mpq_cmp(x.d_n, y.d_n) <= 0;
    }

    friend bool operator>(const Impl& x, const Impl& y) {
      return mpq_cmp(x.d_n, y.d_n) > 0;
    }

    friend bool operator>=(const Impl& x, const Impl& y) {
      return mpq_cmp(x.d_n, y.d_n) >= 0;
    }

    //! Addition
    friend Impl operator+(const Impl& x, const Impl& y) {
      Impl res;
      mpq_add(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Subtraction
    friend Impl operator-(const Impl& x, const Impl& y) {
      Impl res;
      mpq_sub(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Multiplication
    friend Impl operator*(const Impl& x, const Impl& y) {
      Impl res;
      mpq_mul(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Division
    friend Impl operator/(const Impl& x, const Impl& y) {
      Impl res;
      mpq_div(res.d_n, x.d_n, y.d_n);
      return res;
    }

    friend Impl operator%(const Impl& x, const Impl& y) {
      DebugAssert(x.isInteger() && y.isInteger(),
		  "Impl % Impl: x and y must be integers");
      mpz_t res;
      mpz_init(res);
      // Put the remainder directly into 'res'
      mpz_fdiv_r(res, mpq_numref(x.d_n), mpq_numref(y.d_n));
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    //! Compute the remainder of x/y
    friend Impl mod(const Impl& x, const Impl& y) {
      DebugAssert(x.isInteger() && y.isInteger(),
		  "Rational::Impl::mod(): x="+x.toString()
		  +", y="+y.toString());
      mpz_t res;
      mpz_init(res);
      mpz_mod(res, mpq_numref(x.d_n), mpq_numref(y.d_n));
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl intRoot(const Impl& x, unsigned long int y) {
      DebugAssert(x.isInteger(),
		  "Rational::Impl::intRoot(): x="+x.toString());
      mpz_t res;
      mpz_init(res);
      int exact = mpz_root(res, mpq_numref(x.d_n), y);
      if (!exact) {
        mpz_set_ui(res, 0);
      }
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl gcd(const Impl& x, const Impl& y) {
      DebugAssert(x.isInteger() && y.isInteger(),
		  "Rational::Impl::gcd(): x="+x.toString()
		  +", y="+y.toString());
      TRACE("rational", "Impl::gcd(", x, ", "+y.toString()+") {");
      mpz_t res;
      mpz_init(res);
      mpz_gcd(res, mpq_numref(x.d_n), mpq_numref(y.d_n));
      Impl r(res);
      mpz_clear(res);
      TRACE("rational", "Impl::gcd => ", r, "}");
      return r;
    }

    friend Impl lcm(const Impl& x, const Impl& y) {
      DebugAssert(x.isInteger() && y.isInteger(),
		  "Rational::Impl::lcm(): x="+x.toString()
		  +", y="+y.toString());
      mpz_t res;
      mpz_init(res);
      mpz_lcm(res, mpq_numref(x.d_n), mpq_numref(y.d_n));
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    //! Print to string
    string toString(int base = 10) const {
      char* str = (char*)malloc(mpz_sizeinbase(mpq_numref(d_n), base)
				+mpz_sizeinbase(mpq_denref(d_n), base)+3);
      mpq_get_str(str, base, d_n);
      string res(str);
      free(str);
      return res;
    }

    //! Printing to ostream
    friend ostream& operator<<(ostream& os, const Rational::Impl& n) {
      return os << n.toString();
    }

  };

  // Constructor from a pair of integers
  Rational::Impl::Impl(long int n, long int d) {
    mpq_init(d_n);
    DebugAssert(d > 0, "Rational::Impl(long n, long d): d = "+int2string(d));
    mpq_set_si(d_n, n, (unsigned long int)d);
    canonicalize();
  }

  // Constructor from a pair of unsigned integers
  Rational::Impl::Impl(unsigned int n, unsigned int d,
		       unsigned int /* dummy arg, to disambiguate */) {
    mpq_init(d_n);
    mpq_set_ui(d_n, n, (unsigned long int)d);
    canonicalize();
  }

  // Constructor from a string
  Rational::Impl::Impl(const string &n, int base) {
    mpq_init(d_n);
    mpq_set_str(d_n, n.c_str(), base);
    canonicalize();
  }

  // Constructor from a pair of strings
  Rational::Impl::Impl(const string &n, const string& d, int base) {
    mpq_init(d_n);
    mpq_set_str(d_n, (n+"/"+d).c_str(), base);
    canonicalize();
  }

  Rational::Impl Rational::Impl::operator-() const {
    Impl res;
    mpq_neg(res.d_n, d_n);
    return res;
  }

  Rational::Impl Rational::Impl::floor() const {
    mpz_t res;
    mpz_init(res);
    mpz_fdiv_q(res, mpq_numref(d_n), mpq_denref(d_n));
    Impl r(res);
    mpz_clear(res);
    return r;
  }

  Rational::Impl Rational::Impl::ceil() const {
    mpz_t res;
    mpz_init(res);
    mpz_cdiv_q(res, mpq_numref(d_n), mpq_denref(d_n));
    Impl r(res);
    mpz_clear(res);
    return r;
  }

  bool Rational::Impl::isInteger() const {
    bool res(mpz_cmp_ui(mpq_denref(d_n), 1) == 0);
    TRACE("rational", "Impl::isInteger(", *this,
	  ") => "+string(res? "true" : "false"));
    return res;
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

  Rational::Rational(const Unsigned& n): d_n(new Impl(n.toString(), 10)) {
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
#ifdef _DEBUG_RATIONAL_
    int &num_deleted = getDeleted();
    num_deleted++;
    printStats();
#endif
    delete d_n;
  }

  // Get components
  Rational Rational::getNumerator() const
    { return Rational(d_n->getNum()); }
  Rational Rational::getDenominator() const
    { return Rational(d_n->getDen()); }

  bool Rational::isInteger() const { return d_n->isInteger(); }

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
    TRACE("rational", "checkInt(", n, ")");
    DebugAssert(n.isInteger(),
		"CVC3::Rational::" + funName
		+ ": argument is not an integer: " + n.toString());
  }

    /* Computes gcd and lcm on *integer* values. Result is always a
       positive integer.  In this implementation, it is guaranteed by
       GMP. */

  Rational gcd(const Rational &x, const Rational &y) {
    checkInt(x, "gcd(*x*,y)");
    checkInt(y, "gcd(x,*y*)");
    return Rational(gcd(*x.d_n, *y.d_n));
  }

  Rational gcd(const vector<Rational> &v) {
    Rational::Impl g(1,1), zero;
    if(v.size() > 0) {
      checkInt(v[0], "gcd(vector<Rational>[0])");
      g = *v[0].d_n;
    }
    for(size_t i=1; i<v.size(); i++) {
      checkInt(v[i], "gcd(vector<Rational>)");
      if(g == zero)
	g = *(v[i].d_n);
      else if(*(v[i].d_n) != zero)
	g = gcd(g, *(v[i].d_n));
    }
    return Rational(g);
  }

  Rational lcm(const Rational &x, const Rational &y) {
    checkInt(x, "lcm(*x*,y)");
    checkInt(y, "lcm(x,*y*)");
    return Rational(lcm(*x.d_n, *y.d_n));
  }

  Rational lcm(const vector<Rational> &v) {
    Rational::Impl g(1,1), zero;
    for(size_t i=0; i<v.size(); i++) {
      checkInt(v[i], "lcm(vector<Rational>)");
      if(*v[i].d_n != zero)
	g = lcm(g, *v[i].d_n);
    }
    return Rational(g);
  }

  Rational abs(const Rational &x) {
    if(x<0) return -x;
    return x;
  }

  Rational floor(const Rational &x) {
    return Rational(x.d_n->floor());
  }

  Rational ceil(const Rational &x) {
    return Rational(x.d_n->ceil());
  }

  Rational mod(const Rational &x, const Rational &y) {
    checkInt(x, "mod(*x*,y)");
    checkInt(y, "mod(x,*y*)");
    return(Rational(mod(*x.d_n, *y.d_n)));
  }

  Rational intRoot(const Rational& base, unsigned long int n) {
    checkInt(base, "intRoot(*x*,y)");
    return Rational(intRoot(*base.d_n, n));
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
    return Rational(-(*d_n));
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
    return d_n->getInt();
  }

  unsigned int Rational::getUnsigned() const {
    checkInt(*this, "getUnsigned()");
    return d_n->getUnsigned();
  }

  Unsigned Rational::getUnsignedMP() const {
    checkInt(*this, "getUnsignedMP()");
    return d_n->getUnsignedMP();
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
      return Rational((*n1.d_n) + (*n2.d_n));
    }

    Rational operator-(const Rational &n1, const Rational &n2) {
      return Rational((*n1.d_n) - (*n2.d_n));
    }

    Rational operator*(const Rational &n1, const Rational &n2) {
      return Rational((*n1.d_n) * (*n2.d_n));
    }

    Rational operator/(const Rational &n1, const Rational &n2) {
      return Rational((*n1.d_n) / (*n2.d_n));
    }

    Rational operator%(const Rational &n1, const Rational &n2) {
      return Rational((*n1.d_n) % (*n2.d_n));
    }

  //! Implementation of the forward-declared internal class
  class Unsigned::Impl {
    mpz_t d_n;
  public:
    //! Default Constructor
    Impl() { mpz_init(d_n); }
    //! Copy constructor (assumes x is canonicalized)
    Impl(const Impl &x) { mpz_init(d_n); mpz_set(d_n, x.d_n); }
    //! Constructor from mpz_t
    Impl(const mpz_t n) {
      mpz_init(d_n);
      mpz_set(d_n, n);
    }
    //! Constructor from an unsigned integer
    Impl(unsigned int n);
    //! Constructor from a string
    Impl(const string &n, int base);
    // Destructor
    virtual ~Impl() { mpz_clear(d_n); }

    //! Assignment
    Impl& operator=(const Impl& x) {
      if(this == &x) return *this;
      mpz_set(d_n, x.d_n);
      return *this;
    }

    int getInt() const {
      // Check for overflow
      static Impl max((int)INT_MAX);
      FatalAssert(*this <= max,
                  "Unsigned::getInt(): Arithmetic overflow for "
                  +toString());
      return mpz_get_si(d_n);
    }

    unsigned long getUnsigned() const {
      // Check for overflow
      static Impl max(UINT_MAX);
      FatalAssert(*this <= max,
                  "Unsigned::getUnsigned(): Arithmetic overflow for "
                  +toString());
      return mpz_get_ui(d_n);
    }

    //! Unary minus
    Impl operator-() const;

    //! Equality
    friend bool operator==(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) == 0;
    }

    //! Dis-equality
    friend bool operator!=(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) != 0;
    }
    //! Less than
    friend bool operator<(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) < 0;
    }

    friend bool operator<=(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) <= 0;
    }

    friend bool operator>(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) > 0;
    }

    friend bool operator>=(const Impl& x, const Impl& y) {
      return mpz_cmp(x.d_n, y.d_n) >= 0;
    }

    //! Addition
    friend Impl operator+(const Impl& x, const Impl& y) {
      Impl res;
      mpz_add(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Subtraction
    friend Impl operator-(const Impl& x, const Impl& y) {
      Impl res;
      mpz_sub(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Multiplication
    friend Impl operator*(const Impl& x, const Impl& y) {
      Impl res;
      mpz_mul(res.d_n, x.d_n, y.d_n);
      return res;
    }

    //! Division
    friend Impl operator/(const Impl& x, const Impl& y) {
      Impl res;
      mpz_div(res.d_n, x.d_n, y.d_n);
      return res;
    }

    friend Impl operator%(const Impl& x, const Impl& y) {
      mpz_t res;
      mpz_init(res);
      // Put the remainder directly into 'res'
      mpz_fdiv_r(res, x.d_n, y.d_n);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl operator<<(const Impl& x, unsigned y) {
      mpz_t res;
      mpz_init(res);
      mpz_mul_2exp (res, x.d_n, y);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl operator&(const Impl& x, const Impl& y) {
      mpz_t res;
      mpz_init(res);
      mpz_and (res, x.d_n, y.d_n);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    //! Compute the remainder of x/y
    friend Impl mod(const Impl& x, const Impl& y) {
      mpz_t res;
      mpz_init(res);
      mpz_mod(res, x.d_n, y.d_n);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl intRoot(const Impl& x, unsigned long int y) {
      mpz_t res;
      mpz_init(res);
      int exact = mpz_root(res, x.d_n, y);
      if (!exact) {
        mpz_set_ui(res, 0);
      }
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl gcd(const Impl& x, const Impl& y) {
      mpz_t res;
      mpz_init(res);
      mpz_gcd(res, x.d_n, y.d_n);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    friend Impl lcm(const Impl& x, const Impl& y) {
      mpz_t res;
      mpz_init(res);
      mpz_lcm(res, x.d_n, y.d_n);
      Impl r(res);
      mpz_clear(res);
      return r;
    }

    //! Print to string
    string toString(int base = 10) const {
      char* str = (char*)malloc(mpz_sizeinbase(d_n, base)+2);
      mpz_get_str(str, base, d_n);
      string res(str);
      free(str);
      return res;
    }

    //! Printing to ostream
    friend ostream& operator<<(ostream& os, const Unsigned::Impl& n) {
      return os << n.toString();
    }

  };

  // Constructor from a pair of unsigned integers
  Unsigned::Impl::Impl(unsigned int n) {
    mpz_init(d_n);
    mpz_set_ui(d_n, n);
  }

  // Constructor from a string
  Unsigned::Impl::Impl(const string &n, int base) {
    mpz_init(d_n);
    mpz_set_str(d_n, n.c_str(), base);
  }

  Unsigned::Impl Unsigned::Impl::operator-() const {
    Impl res;
    mpz_neg(res.d_n, d_n);
    return res;
  }

  //! Default constructor
  Unsigned::Unsigned() : d_n(new Impl) { }
  //! Copy constructor
  Unsigned::Unsigned(const Unsigned &n) : d_n(new Impl(*n.d_n)) { }

  Unsigned::Unsigned(int n) : d_n(new Impl((unsigned)n)) { }

  Unsigned::Unsigned(unsigned n) : d_n(new Impl(n)) { }
  //! Private constructor
  Unsigned::Unsigned(const Impl& t): d_n(new Impl(t)) { }
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


  // Check that argument is an int and print an error message otherwise

    /* Computes gcd and lcm on *integer* values. Result is always a
       positive integer.  In this implementation, it is guaranteed by
       GMP. */

  Unsigned gcd(const Unsigned &x, const Unsigned &y) {
    return Unsigned(gcd(*x.d_n, *y.d_n));
  }

  Unsigned gcd(const vector<Unsigned> &v) {
    Unsigned::Impl g(1), zero;
    if(v.size() > 0) {
      g = *v[0].d_n;
    }
    for(size_t i=1; i<v.size(); i++) {
      if(g == zero)
	g = *(v[i].d_n);
      else if(*(v[i].d_n) != zero)
	g = gcd(g, *(v[i].d_n));
    }
    return Unsigned(g);
  }

  Unsigned lcm(const Unsigned &x, const Unsigned &y) {
    return Unsigned(lcm(*x.d_n, *y.d_n));
  }

  Unsigned lcm(const vector<Unsigned> &v) {
    Unsigned::Impl g(1), zero;
    for(size_t i=0; i<v.size(); i++) {
      if(*v[i].d_n != zero)
	g = lcm(g, *v[i].d_n);
    }
    return Unsigned(g);
  }

  Unsigned mod(const Unsigned &x, const Unsigned &y) {
    return(Unsigned(mod(*x.d_n, *y.d_n)));
  }

  Unsigned intRoot(const Unsigned& base, unsigned long int n) {
    return Unsigned(intRoot(*base.d_n, n));
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
    return Unsigned((*n1.d_n) + (*n2.d_n));
  }

  Unsigned operator-(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned((*n1.d_n) - (*n2.d_n));
  }

  Unsigned operator*(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned((*n1.d_n) * (*n2.d_n));
  }

  Unsigned operator/(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned((*n1.d_n) / (*n2.d_n));
  }

  Unsigned operator%(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned((*n1.d_n) % (*n2.d_n));
  }

  Unsigned operator<<(const Unsigned &n1, unsigned n2) {
    return Unsigned((*n1.d_n) << n2);
  }

  Unsigned operator&(const Unsigned &n1, const Unsigned &n2) {
    return Unsigned((*n1.d_n) & (*n2.d_n));
  }

  Unsigned Rational::Impl::getUnsignedMP() const {
    return Unsigned(Unsigned::Impl(mpq_numref(d_n)));
  }


} /* close namespace */

#endif
