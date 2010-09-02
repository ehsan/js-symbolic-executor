(*
 * Copyright 2010 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

type symbolId = int

type locId = int

type unop =
  | Not
  | Negative

let sprintUnop = function
  | Not -> "!"
  | Negative -> "-"

type binop =
  | Plus
  | Minus
  | Times
  | Divide
  | Modulo
  | And
  | Or
  | GreaterThan
  | LessThan
  | GreaterThanEqualTo
  | LessThanEqualTo
  | Equal
  | Unequal

let sprintBinop = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | Modulo -> "%"
  | And -> "&&"
  | Or -> "||"
  | GreaterThan -> ">"
  | LessThan -> "<"
  | GreaterThanEqualTo -> ">="
  | LessThanEqualTo -> "<"
  | Equal -> "==="
  | Unequal -> "!=="

type ('index,'elt) arr = Empty | Store of ('index,'elt) arr * 'index * 'elt

type ('a,'b) elt = Base of 'b | Read of ('a,'b) arr * 'a

type js =
  | Symbol of symbolId
  | Null
  | Undefined
  | Bool of bool
  | Num of int (* really should be float *)
  | String of string
  | Location of locId
  | Unop of unop * js
  | Binop of binop * js * js
  | Ite of js * js * js
  | GetProp of js * js

let rec sprintJsExpr = function
  | Symbol s -> Format.sprintf "sym%d" s
  | Null -> "null"
  | Undefined -> "undef"
  | Bool b -> string_of_bool b
  | Num n -> string_of_int n
  | String s -> Format.sprintf "'%s'" s
  | Location locId -> Format.sprintf "loc%d" locId
  | Unop (op, expr) -> Format.sprintf "(%s %s)" (sprintUnop op) (sprintJsExpr expr)
  | Binop (op, expr1, expr2) -> Format.sprintf "(%s %s %s)" (sprintJsExpr expr1) (sprintBinop op) (sprintJsExpr expr2)
  | Ite (expr1, expr2, expr3) -> Format.sprintf "(%s ? %s : %s)" (sprintJsExpr expr1) (sprintJsExpr expr2) (sprintJsExpr expr3)
  | GetProp (e1, e2) -> Format.sprintf "%s[%s]" (sprintJsExpr e1) (sprintJsExpr e2)

type var0
module Phantom : sig
  type 'a t
  val var : string -> var0 t
  val toString : 'a t -> string
end = struct
  type 'a t = string
  let var x = x
  let toString x = x
end

type var = var0 Phantom.t
let makeVar = Phantom.var

module MapFromVar = Map.Make(struct type t = var let compare = compare end)

module E = MapFromVar

type env = js E.t (* This is currently called the symbolicExecution object's 'memory' *)

type obj = ObjEmpty | ObjStore of obj * js * js | Read of heap_map * js
and heap_map = (js, obj) arr

type heap = (locId * heap_map) (* The next objId to use, and the actual heap *)

(* By default, print to stdout *)
let printEnv ?(ppf=Format.std_formatter) (env:env) =
  Format.fprintf ppf "env{\n";
  E.iter (fun var expr ->
	    Format.fprintf ppf "  ";
	    Format.fprintf ppf "%s -> %s,\n" (Phantom.toString var) (sprintJsExpr expr)) env;
  Format.fprintf ppf "}\n"

let rec arrIter f arr = match arr with
  | Empty -> ()
  | Store (arr, index, value) -> f index value; arrIter f arr
;;

let rec printObj ?(ppf=Format.std_formatter) (obj:obj) =
  match obj with
    | ObjEmpty -> Format.fprintf ppf "{}"
    | ObjStore(obj, prop, value) ->
	Format.fprintf ppf "(upd %a %s %s)" (fun ppf obj -> printObj ~ppf obj) obj (sprintJsExpr prop) (sprintJsExpr value)
    | Read (heap_map, loc) -> Format.fprintf ppf "(read %a %s)" (fun pff map -> printHeapMap ~ppf map) heap_map (sprintJsExpr loc)
and printHeapMap ?(ppf=Format.std_formatter) (heap_map:heap_map) =
  match heap_map with
    | Empty -> Format.fprintf ppf "_"
    | Store (heapmap, loc, value) ->
	Format.fprintf ppf "(write %a %s %a)"
	  (fun ppf heapmap -> printHeapMap ~ppf heapmap) heapmap
	  (sprintJsExpr loc)
	  (fun ppf obj -> printObj ~ppf obj) value
;;
let printHeap ?(ppf=Format.std_formatter) (_,map) = printHeapMap ~ppf map
;;

let createObj (locId, map : heap) : locId * heap =
  (locId, (succ locId, Store (map, Location locId, ObjEmpty)))
;;

(* x = ... *)
let varGetsExpr (var:var) (expr:js) (env:env) : env =
  let env = E.add var expr env in
  printEnv env;
  env
;;

(* x = {} *)
let varGetsNewObj (var:var) (env:env) (heap:heap) : env * heap =
  let locId, heap = createObj heap in
  let env = E.add var (Location locId) env in
  let result = (env, heap) in
  printEnv env; printHeap heap;
  result
;;

let lookupVar var env =
  try E.find var env
  with Not_found -> Undefined
;;

let lookupVarByName varName env =
  let var = makeVar varName in
  try E.find var env
  with Not_found -> Undefined
;;

(* obj[prop] = ... *)
let varPropertyGetsExpr (objVar:var) (propVar:var) (expr:js) (env:env) (heap:heap) : heap =
  let loc = lookupVar objVar env
  and propExpr = lookupVar propVar env in
  let obj = Read (snd heap, loc) in
  let updatedObj = ObjStore (obj, propExpr, expr) in
  let heap = (fst heap, Store (snd heap, loc, updatedObj)) in
  printHeap heap;
  heap
;;

let (env:env) = E.empty;;
let (heap:heap) = 0,Empty;;

let print str = Format.printf "js> %s" str;;

print "x = {};\n";;
let env, heap = varGetsNewObj (makeVar "x") env heap;;

print "prop='a';\n";;
let env = varGetsExpr (makeVar "prop") (String "a") env;;

print "newObj={};\n";;
let env, heap = varGetsNewObj (makeVar "newObj") env heap;;
print "x[prop]=newObj;\n";;
let heap = varPropertyGetsExpr (makeVar "x") (makeVar "prop") (lookupVarByName "newObj" env) env heap;;

print "prop='b';\n";;
let env = varGetsExpr (makeVar "prop") (String "b") env;;

print "x[prop]=x;\n";;
let heap = varPropertyGetsExpr (makeVar "x") (makeVar "prop") (lookupVarByName "x" env) env heap;;

print "y = sym0 ? 'a' : 'b';\n";;
let env = varGetsExpr (makeVar "y") (Ite (Symbol 0, String "a", String "b")) env;;

(* While technically allowed, this would do nothing because it would create a
   new object that is then immediately thrown away, so I don't mind that I
   currently don't handle this. (See ECMA-262, Ed. 3, 11.13.1, 11.2.1, 9.9,
   8.7.2, and maybe 8.6.2.2.) Currently, though, it doesn't notice that y is not
   an object. That seems not good. *)
print "y[c]='hi';\n";;
let heap = varPropertyGetsExpr (makeVar "y") (makeVar "c") (String "hi") env heap;;

(* This is, in essence, a symbolic read. It should work *)
print "x[y] = true;\n";;
let heap = varPropertyGetsExpr (makeVar "x") (makeVar "y") (Bool true) env heap;;

print "x[prop] = 8;\n";;
let heap = varPropertyGetsExpr (makeVar "x") (makeVar "prop") (Num 8) env heap;;

(* Below is a 'double dereference', which would be nice to handle, but isn't the top priority *)
Format.printf "\tx[y].f = 7, in three stages:\n";;
print "z = x[y];\n";;
let env = varGetsExpr (makeVar "z") (GetProp (lookupVarByName "x" env, lookupVarByName "y" env)) env;;
print "prop='f';\n";;
let env = varGetsExpr (makeVar "prop") (String "f") env;;
print "z[f] = 7;\n";;
let heap = varPropertyGetsExpr (makeVar "z") (makeVar "prop") (Num 7) env heap;;
