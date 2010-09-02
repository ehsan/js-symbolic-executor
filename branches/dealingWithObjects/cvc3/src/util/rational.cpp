/*****************************************************************************/
/*!
 * \file rational.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Dec 12 22:00:18 GMT 2002
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/
// Class: Rational
// Author: Sergey Berezin, 12/12/2002 (adapted from Bignum)
//
// Description: Implementation of class Rational.  See comments in
// rational.h file.
///////////////////////////////////////////////////////////////////////////////

#ifdef RATIONAL_GMPXX

#include <gmpxx.h>
#include "compat_hash_set.h"
#include "rational.h"

namespace CVC3 {

  using namespace std;

  // Implementation of the forward-declared internal class
  class Rational::Impl : public mpq_class {
  public:
    //    mpz_class _n;
    // Constructors
    Impl() : mpq_class() { }
    // Constructor from integer
    //    Impl(const mpz_class &x) : mpq_class(x) { }
    // Constructor from rational
    Impl(const mpq_class &x) : mpq_class(x) { }
    // Copy constructor
    Impl(const Impl &x) : mpq_class(x) { }
    // From pair of integers / strings
    Impl(int n, int d) : mpq_class(n,d) { canonicalize(); }
    Impl(const mpz_class& n, const mpz_class& d)
      : mpq_class(n,d) { canonicalize(); }
    // From string(s)
    Impl(const string &n, int base): mpq_class(n, base) { canonicalize(); }
    Impl(const string &n, const string& d, int base)
      : mpq_class(n + "/" + d, base)  { canonicalize(); }
    // Destructor
    virtual ~Impl() { }
    // Getting numerator and denominator.  DON NOT ASSIGN to the result
    mpz_class getNum() { return get_num(); }
    mpz_class getDen() { return get_den(); }
  };

  // Constructors
  Rational::Rational() : d_n(new Impl) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }
    // Copy constructor
  Rational::Rational(const Rational &n) : d_n(new Impl(*n.d_n)) {
#ifdef _DEBUG_RATIONAL_
    int &num_created = getCreated();
    num_created++;
    printStats();
#endif
  }

  // Private constructor
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
    mpz_class g;
    checkInt(x, "gcd(*x*,y)");
    checkInt(y, "gcd(x,*y*)");
    mpz_gcd(g.get_mpz_t(), x.d_n->get_num_mpz_t(), y.d_n->get_num_mpz_t());
    return Rational(Rational::Impl(g,1));
  }
 
  Rational gcd(const vector<Rational> &v) {
    mpz_class g(1);
    if(v.size() > 0) {
      checkInt(v[0], "gcd(vector<Rational>[0])");
      g = v[0].d_n->getNum();
    }
    for(unsigned i=1; i<v.size(); i++) {
      checkInt(v[i], "gcd(vector<Rational>)");
      if(*v[i].d_n != 0)
	mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), v[i].d_n->get_num_mpz_t());
    }
    return Rational(Rational::Impl(g,1));
  }

  Rational lcm(const Rational &x, const Rational &y) {
    mpz_class g;
    checkInt(x, "lcm(*x*,y)");
    checkInt(y, "lcm(x,*y*)");
    mpz_lcm(g.get_mpz_t(), x.d_n->get_num_mpz_t(), y.d_n->get_num_mpz_t());
    return Rational(Rational::Impl(g, 1));
  }

  Rational lcm(const vector<Rational> &v) {
    mpz_class g(1);
    for(unsigned i=0; i<v.size(); i++) {
      checkInt(v[i], "lcm(vector<Rational>)");
      if(*v[i].d_n != 0)
	mpz_lcm(g.get_mpz_t(), g.get_mpz_t(), v[i].d_n->get_num_mpz_t());
    }
    return Rational(Rational::Impl(g,1));
  }

  Rational abs(const Rational &x) {
    return Rational(Rational::Impl(abs(*x.d_n)));
  }

  Rational floor(const Rational &x) {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), x.d_n->get_num_mpz_t(), x.d_n->get_den_mpz_t());
    return Rational(Rational::Impl(q,1));
  }

  Rational ceil(const Rational &x) {
    mpz_class q;
    mpz_cdiv_q(q.get_mpz_t(), x.d_n->get_num_mpz_t(), x.d_n->get_den_mpz_t());
    return Rational(Rational::Impl(q,1));
  }

  Rational mod(const Rational &x, const Rational &y) {
    checkInt(x, "mod(*x*,y)");
    checkInt(y, "mod(x,*y*)");
    mpz_class r;
    mpz_mod(r.get_mpz_t(), x.d_n->get_num_mpz_t(), y.d_n->get_num_mpz_t());
    return(Rational(Rational::Impl(r,1)));
  }

  Rational intRoot(const Rational& base, unsigned long int n)
  {
    return Rational(Rational::Impl(0,1));
  }

  string Rational::toString(int base) const {
    char *tmp = mpq_get_str(NULL, base, d_n->get_mpq_t());
    string res(tmp);
//    delete tmp;
    free(tmp);
    return(res);
  }

  size_t Rational::hash() const {
    std::hash<const char *> h;
    return h(toString().c_str());
  }
  
  void Rational::print() const {
    cout << (*d_n) << endl;
  }



  // Unary minus
  Rational Rational::operator-() const {
    return Rational(Rational::Impl(- (*d_n)));
  }
  
  Rational &Rational::operator+=(const Rational &n2) {
    *d_n += (*n2.d_n);
    return *this;
  }
  
  Rational &Rational::operator-=(const Rational &n2) {
    *d_n -= (*n2.d_n);
    return *this;
  }
  
  Rational &Rational::operator*=(const Rational &n2) {
    *d_n *= (*n2.d_n);
    return *this;
  }
  
  Rational &Rational::operator/=(const Rational &n2) {
    *d_n /= (*n2.d_n);
    return *this;
  }

  int Rational::getInt() const {
    checkInt(*this, "getInt()");
    return mpz_get_si(d_n->get_num_mpz_t());
  }

  unsigned int Rational::getUnsigned() const {
    checkInt(*this, "getUnsigned()");
    return mpz_get_ui(d_n->get_num_mpz_t());
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
      return Rational(Rational::Impl(*n1.d_n + *n2.d_n));
    }


  // Implementation of the forward-declared internal class
  class Unsigned::Impl : public mpz_class {
  public:
    //    mpz_class _n;
    // Constructors
    Impl() : mpz_class() { }
    // Constructor from integer
    //    Impl(const mpz_class &x) : mpq_class(x) { }
    // Constructor from rational
    Impl(const mpz_class &x) : mpz_class(x) { }
    // Copy constructor
    Impl(const Impl &x) : mpz_class(x) { }
    // From pair of integers / strings
    Impl(int n) : mpz_class(n) { }
    Impl(const mpz_class& n, const mpz_class& d)
      : mpq_class(n,d) { canonicalize(); }
    // From string(s)
    Impl(const string &n, int base): mpz_class(n, base) { }
    // Destructor
    virtual ~Impl() { }
  };

  // Constructors
  Unsigned::Unsigned() : d_n(new Impl) { }
  // Copy constructor
  Unsigned::Unsigned(const Unsigned &n) : d_n(new Impl(*n.d_n)) { }

  // Private constructor
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


    /* Computes gcd and lcm on *integer* values. Result is always a
       positive integer.  In this implementation, it is guaranteed by
       GMP. */

  Unsigned gcd(const Unsigned &x, const Unsigned &y) {
    mpz_class g;
    mpz_gcd(g, *(x.d_n), *(y.d_n));
    return Unsigned(Unsigned::Impl(g));
  }
 
  Unsigned gcd(const vector<Unsigned> &v) {
    mpz_class g(1);
    if(v.size() > 0) {
      g = *(v[0].d_n);
    }
    for(unsigned i=1; i<v.size(); i++) {
      if(*v[i].d_n != 0)
	mpz_gcd(g, g, *(v[i].d_n));
    }
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned lcm(const Unsigned &x, const Unsigned &y) {
    mpz_class g;
    mpz_lcm(g, *x.d_n, *y.d_n);
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned lcm(const vector<Unsigned> &v) {
    mpz_class g(1);
    for(unsigned i=0; i<v.size(); i++) {
      if(*v[i].d_n != 0)
	mpz_lcm(g, g, *v[i].d_n);
    }
    return Unsigned(Unsigned::Impl(g));
  }

  Unsigned abs(const Unsigned &x) {
    return Unsigned(Unsigned::Impl(abs(*x.d_n)));
  }

  Unsigned mod(const Unsigned &x, const Unsigned &y) {
    mpz_class r;
    mpz_mod(r, *x.d_n, *y.d_n);
    return(Unsigned(Unsigned::Impl(r)));
  }

  Unsigned intRoot(const Unsigned& base, unsigned long int n)
  {
    return Unsigned(Unsigned::Impl(0,1));
  }

  string Unsigned::toString(int base) const {
    char *tmp = mpz_get_str(NULL, base, *d_n);
    string res(tmp);
//    delete tmp;
    free(tmp);
    return(res);
  }

  size_t Unsigned::hash() const {
    std::hash<const char *> h;
    return h(toString().c_str());
  }
  
  void Unsigned::print() const {
    cout << (*d_n) << endl;
  }



  // Unary minus
  Unsigned Unsigned::operator-() const {
    return Unsigned(Unsigned::Impl(- (*d_n)));
  }
  
  Unsigned &Unsigned::operator+=(const Unsigned &n2) {
    *d_n += (*n2.d_n);
    return *this;
  }
  
  Unsigned &Unsigned::operator-=(const Unsigned &n2) {
    *d_n -= (*n2.d_n);
    return *this;
  }
  
  Unsigned &Unsigned::operator*=(const Unsigned &n2) {
    *d_n *= (*n2.d_n);
    return *this;
  }
  
  Unsigned &Unsigned::operator/=(const Unsigned &n2) {
    *d_n /= (*n2.d_n);
    return *this;
  }

  int Unsigned::getInt() const {
    return mpz_get_si(*d_n);
  }

  unsigned int Unsigned::getUnsigned() const {
    return mpz_get_ui(*d_n);
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
      return Unsigned(Unsigned::Impl(*n1.d_n + *n2.d_n));
    }

}; /* close namespace */


#endif
