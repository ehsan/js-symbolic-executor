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

type unOp =
  | Not
  | Negative
  | Typeof

type binOp =
  | OpLT 
  | OpLEq 
  | OpGT 
  | OpGEq  
  | OpIn
  | OpInstanceof
  | OpEq
  | OpNEq
  | OpStrictEq
  | OpStrictNEq
  | OpLAnd
  | OpLOr 
  | OpMul
  | OpDiv
  | OpMod
  | OpSub
  | OpLShift
  | OpSpRShift
  | OpZfRShift
  | OpBAnd
  | OpBXor
  | OpBOr
  | OpAdd

type const =
  | CString of string
  | CRegexp of string * bool * bool
  | CNum of float
  | CInt of int
  | CBool of bool
  | CNull 
  | CUndefined

type var

type label

type expr =
  | ConstExpr of const
  | NewArrayExpr
  | NewObjExpr
  | VarExpr of var
  | BracketExpr of var * var
  | UnopExpr of unOp * var
  | BinopExpr of binOp * var * var
  | IteExpr of var * var * var

type catch =
  | CatchClause of var * stmt

and stmt =
  | EmptyStmt
  | BlockStmt of stmt list (* s1;s2;...;sn *)
  | AssignStmt of var * expr (* v = e *)
  | CreateObj of var (* v = {} *)
  | CreateArray of var (* v = [] *)
  | AssignPropStmt of var * var * var (* v1[v2] = v3 *)
  | CallExpr of var option * var * var list (* [v1 =] v2.apply(vs) *)
  | FuncExpr of var option * var list * var list * stmt (* [v =] function(vs1) { var vs2; stmt } *)
  | IfStmt of var * stmt * stmt
  | LoopStmt of stmt
  | BreakStmt
  | BreakToStmt of label
  | ContinueStmt
  | ContinueToStmt of label
  | LabelledStmt of label * stmt
  | ForInStmt of var * var * stmt (* for (v1 in v2) { stmt } *)
  | TryStmt of stmt * catch list * stmt (* (tryBlock, catchBlocks, finallyBlock) *)
  | ThrowStmt of var
  | ReturnStmt of var
