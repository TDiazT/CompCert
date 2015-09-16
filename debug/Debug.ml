(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open C
open Camlcoq

(* Interface for generating and printing debug information *)

(* Record used for stroring references to the actual implementation functions *)
type implem = 
    {
     mutable init: string -> unit;
     mutable atom_function: ident -> atom -> unit;
     mutable atom_global_variable: ident -> atom -> unit;
     mutable set_composite_size: ident -> struct_or_union -> int option -> unit;
     mutable set_member_offset: ident -> string -> int -> unit;
     mutable set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
     mutable insert_global_declaration: Env.t -> globdecl -> unit;
     mutable add_fun_addr: atom -> (int * int) -> unit
   }

let implem =
  {
   init = (fun _ -> ());
   atom_function = (fun _ _ -> ());
   atom_global_variable = (fun _ _ -> ());
   set_composite_size = (fun _ _ _ -> ());
   set_member_offset = (fun _ _  _ -> ());
   set_bitfield_offset = (fun _ _ _ _ _ -> ());
   insert_global_declaration = (fun _ _ -> ());
   add_fun_addr = (fun _ _ -> ());
 }

let init () =
  if !Clflags.option_g then begin
    implem.init <- DebugInformation.init;
    implem.atom_function <- DebugInformation.atom_function;
    implem.atom_global_variable <- DebugInformation.atom_global_variable;
    implem.set_composite_size <- DebugInformation.set_composite_size;
    implem.set_member_offset <- DebugInformation.set_member_offset;
    implem.set_bitfield_offset <- DebugInformation.set_bitfield_offset;
    implem.insert_global_declaration <- DebugInformation.insert_global_declaration;
    implem.add_fun_addr <- DebugInformation.add_fun_addr;
  end else begin
    implem.init <- (fun _ -> ());
    implem.atom_function <- (fun _ _ -> ());
    implem.atom_global_variable <- (fun _ _ -> ());
    implem.set_composite_size <- (fun _ _ _ -> ());
    implem.set_member_offset <- (fun _ _ _ -> ());
    implem.set_bitfield_offset <- (fun _ _ _ _ _ -> ());
    implem.insert_global_declaration <- (fun _ _ -> ());
    implem.add_fun_addr <- (fun _ _ -> ())
  end

let init_compile_unit name = implem.init name
let atom_function id atom = implem.atom_function id atom
let atom_global_variable id atom = implem.atom_global_variable id atom
let set_composite_size id sou size = implem.set_composite_size id sou size
let set_member_offset id field off = implem.set_member_offset id field off
let set_bitfield_offset id field off underlying size = implem.set_bitfield_offset id field off underlying size
let insert_global_declaration env dec = implem.insert_global_declaration env dec
let add_fun_addr atom addr = implem.add_fun_addr atom addr
