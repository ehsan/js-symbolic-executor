#ifndef OBJ_H_
#define OBJ_H_

#include "theory_core.h"
#include "theorem_manager.h"
#include "common_proof_rules.h"
#include "command_line_flags.h"
#include "theory_arith.h"
#include <fstream>

#define _CVC3_TRUSTED_

using namespace std;
using namespace CVC3;


//#define DEBUG_MEM_STATS
// flag for testing some cvc3 custom made prof rules
//#define PRINT_MAJOR_METHODS
//#define LRA2_PRIME
//#define OPTIMIZE
//#define IGNORE_NORMALIZE
//#define IGNORE_LETPF_VARS
//#define IGNORE_PRINT_MULTI_LAMBDA

//smart pointer class
template<class T>
class RefPtr
{
public:
   typedef T element_type;
   RefPtr() :_ptr(0L) {}
   RefPtr(T* t):_ptr(t)              { if (_ptr) _ptr->Ref(); }
   RefPtr(const RefPtr& rp):_ptr(rp._ptr)  { if (_ptr) _ptr->Ref(); }
   ~RefPtr()                           { if (_ptr) _ptr->Unref(); _ptr=0; }
   inline RefPtr& operator = (const RefPtr& rp){
      if (_ptr==rp._ptr) return *this;
      T* tmp_ptr = _ptr;
      _ptr = rp._ptr;
      if (_ptr) _ptr->Ref();
      if (tmp_ptr) tmp_ptr->Unref();
      return *this;
   }
   inline RefPtr& operator = (T* ptr){
      if (_ptr==ptr) return *this;
      T* tmp_ptr = _ptr;
      _ptr = ptr;
      if (_ptr) _ptr->Ref();
      if (tmp_ptr) tmp_ptr->Unref();
      return *this;
   }
   inline T& operator*()  { return *_ptr; }
   inline const T& operator*() const { return *_ptr; }
   inline T* operator->() { return _ptr; }
   inline const T* operator->() const   { return _ptr; }
   inline T* get() { return _ptr; }
   inline const T* get() const { return _ptr; }
private:
   T* _ptr;
};

//standard (reference pointer) object
class Obj
{
protected:
  ostringstream oignore;
  int refCount;

  static bool errsInit;
  static ofstream errs;
  static bool indentFlag;

  void indent( std::ostream& s, int ind = 0 ){
    if( ind>0 )
      s << endl;
    if( indentFlag ){
      for( int a=0; a<ind; a++ )
        s << " ";
    }
  }
public:
  Obj(): refCount( 1 ) {}
  virtual ~Obj() {}
  //! get ref count
  int GetRefCount() { return refCount; }
  //! reference
  void Ref(){ refCount++; }
  //! unreference
  void Unref(){
    refCount--;
    if( refCount==0 ){
      delete this;
    }
   }
  static void print_error( const char* c, std::ostream& s ){
    if( !errsInit ){
      errs.open( "errors.txt" );
      errsInit = true;
    }
    errs << c << std::endl;
    s << c;
    exit( 1 );
  }
  static void print_warning( const char* c ){
    if( !errsInit ){
      errs.open( "errors.txt" );
      errsInit = true;
    }
    errs << c << std::endl;
  }
  static void initialize(){
    errsInit = false;
  }
};

#endif
