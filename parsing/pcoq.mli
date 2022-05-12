(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg
open Constrexpr
open Libnames

(** The parser of Coq *)

include Gramlib.Grammar.S
  with type keyword_state := CLexer.keyword_state
   and type te := Tok.t
   and type 'a pattern := 'a Tok.p
   and type 'a with_gstate := 'a
   and type 'a with_kwstate := 'a
   and type 'a with_estate := 'a
   and type 'a mod_estate := 'a

module Lookahead : sig
  type t
  val to_entry : string -> t -> unit Entry.t
  val (>>) : t -> t -> t
  val (<+>) : t -> t -> t
  val lk_empty : t
  val lk_list : t -> t
  val check_no_space : t
  val lk_kw : string -> t
  val lk_kws : string list -> t
  val lk_nat : t
  val lk_ident : t
  val lk_field : t
  val lk_name : t
  val lk_qualid : t
  val lk_ident_except : string list -> t
  val lk_ident_list : t
end

(** When string is not an ident, returns a keyword. *)
val terminal : string -> string Tok.p

(** The parser of Coq is built from three kinds of rule declarations:

   - dynamic rules declared at the evaluation of Coq files (using
     e.g. Notation, Infix, or Tactic Notation)
   - static rules explicitly defined in files g_*.mlg
   - static rules macro-generated by ARGUMENT EXTEND, TACTIC EXTEND and
     VERNAC EXTEND (see e.g. file extratactics.mlg)

   Note that parsing a Coq document is in essence stateful: the parser
   needs to recognize commands that start proofs and use a different
   parsing entry point for them.

   We thus provide two different interfaces: the "raw" parsing
   interface, in the style of camlp5, which provides more flexibility,
   and a more specialize "parse_vernac" one, which will indeed adjust
   the state as needed.

*)

(** Dynamic extension of rules

    For constr notations, dynamic addition of new rules is done in
    several steps:

    - "x + y" (user gives a notation string of type Topconstr.notation)
        |     (together with a constr entry level, e.g. 50, and indications of)
        |     (subentries, e.g. x in constr next level and y constr same level)
        |
        | splitting into tokens by Metasyntax.split_notation_string
        V
      [String "x"; String "+"; String "y"] : symbol_token list
        |
        | interpreted as a mixed parsing/printing production
        | by Metasyntax.analyse_notation_tokens
        V
      [NonTerminal "x"; Terminal "+"; NonTerminal "y"] : symbol list
        |
        | translated to a parsing production by Metasyntax.make_production
        V
      [GramConstrNonTerminal (ETConstr (NextLevel,(BorderProd Left,LeftA)),
                              Some "x");
       GramConstrTerminal ("","+");
       GramConstrNonTerminal (ETConstr (NextLevel,(BorderProd Right,LeftA)),
                              Some "y")]
       : grammar_constr_prod_item list
        |
        | Egrammar.make_constr_prod_item
        V
      Gramext.g_symbol list which is sent to camlp5

    For user level tactic notations, dynamic addition of new rules is
    also done in several steps:

    - "f" constr(x) (user gives a Tactic Notation command)
        |
        | parsing
        V
      [TacTerm "f"; TacNonTerm ("constr", Some "x")]
      : grammar_tactic_prod_item_expr list
        |
        | Metasyntax.interp_prod_item
        V
      [GramTerminal "f";
       GramNonTerminal (ConstrArgType, Aentry ("constr","constr"), Some "x")]
      : grammar_prod_item list
        |
        | Egrammar.make_prod_item
        V
      Gramext.g_symbol list

    For TACTIC/VERNAC/ARGUMENT EXTEND, addition of new rules is done as follows:

    - "f" constr(x) (developer gives an EXTEND rule)
        |
        | macro-generation in tacextend.mlg/vernacextend.mlg/argextend.mlg
        V
      [GramTerminal "f";
       GramNonTerminal (ConstrArgType, Aentry ("constr","constr"), Some "x")]
        |
        | Egrammar.make_prod_item
        V
      Gramext.g_symbol list

*)

(** Parse a string *)

val parse_string : 'a Entry.t -> ?loc:Loc.t -> string -> 'a
val eoi_entry : 'a Entry.t -> 'a Entry.t

val create_generic_entry2 : string ->
  ('a, rlevel) abstract_argument_type -> 'a Entry.t

val register_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Entry.t -> unit
val genarg_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Entry.t

module Prim :
  sig
    open Names
    open Libnames
    val preident : string Entry.t
    val ident : Id.t Entry.t
    val name : lname Entry.t
    val identref : lident Entry.t
    val univ_decl : universe_decl_expr Entry.t
    val ident_decl : ident_decl Entry.t
    val pattern_ident : lident Entry.t
    val base_ident : Id.t Entry.t
    val bignat : string Entry.t
    val natural : int Entry.t
    val bigint : string Entry.t
    val integer : int Entry.t
    val string : string Entry.t
    val lstring : lstring Entry.t
    val reference : qualid Entry.t
    val fields : (Id.t list * Id.t) Entry.t
    val qualid : qualid Entry.t
    val fullyqualid : Id.t list CAst.t Entry.t
    val by_notation : (string * string option) Entry.t
    val smart_global : qualid or_by_notation Entry.t
    val dirpath : DirPath.t Entry.t
    val ne_string : string Entry.t
    val ne_lstring : lstring Entry.t
    val hyp : lident Entry.t
    val var : lident Entry.t [@@ocaml.deprecated "Use Prim.hyp"]
    val bar_cbrace : unit Entry.t
    val strategy_level : Conv_oracle.level Entry.t
  end

module Constr :
  sig
    val constr : constr_expr Entry.t
    val constr_eoi : constr_expr Entry.t
    val lconstr : constr_expr Entry.t
    val binder_constr : constr_expr Entry.t
    val term : constr_expr Entry.t
    val ident : Id.t Entry.t
    val global : qualid Entry.t
    val universe_name : sort_name_expr Entry.t
    val universe : universe_expr Entry.t
    val sort : sort_expr Entry.t
    val sort_family : Sorts.family Entry.t
    val pattern : cases_pattern_expr Entry.t
    val constr_pattern : constr_expr Entry.t
    val cpattern : constr_expr Entry.t
    val closed_binder : local_binder_expr list Entry.t
    val binder : local_binder_expr list Entry.t (* closed_binder or variable *)
    val binders : local_binder_expr list Entry.t (* list of binder *)
    val open_binders : local_binder_expr list Entry.t
    val one_open_binder : kinded_cases_pattern_expr Entry.t
    val one_closed_binder : kinded_cases_pattern_expr Entry.t
    val binders_fixannot : (local_binder_expr list * fixpoint_order_expr option) Entry.t
    val typeclass_constraint : (lname * bool * constr_expr) Entry.t
    val record_declaration : constr_expr Entry.t
    val arg : (constr_expr * explicitation CAst.t option) Entry.t
    val type_cstr : constr_expr Entry.t
  end

module Module :
  sig
    val module_expr : module_ast Entry.t
    val module_type : module_ast Entry.t
  end

(** {5 Type-safe grammar extension} *)

val epsilon_value : ('a -> 'self) -> ('self, _, 'a) Symbol.t -> 'self option

(** {5 Extending the parser without synchronization} *)

val grammar_extend : 'a Entry.t -> 'a extend_statement -> unit
(** Extend the grammar of Coq, without synchronizing it with the backtracking
    mechanism. This means that grammar extensions defined this way will survive
    an undo. *)

(** {5 Extending the parser with summary-synchronized commands} *)

module GramState : Store.S
(** Auxiliary state of the grammar. Any added data must be marshallable. *)

(** {6 Extension with parsing rules} *)

type 'a grammar_command
(** Type of synchronized parsing extensions. The ['a] type should be
    marshallable. *)

type gram_reinit = Gramlib.Gramext.g_assoc * Gramlib.Gramext.position
(** Type of reinitialization data *)

type extend_rule =
| ExtendRule : 'a Entry.t * 'a extend_statement -> extend_rule
| ExtendRuleReinit : 'a Entry.t * gram_reinit * 'a extend_statement -> extend_rule

type 'a grammar_extension = {
  gext_fun : 'a -> GramState.t -> extend_rule list * GramState.t;
  gext_eq : 'a -> 'a -> bool;
}
(** Grammar extension entry point. Given some ['a] and a current grammar state,
    such a function must produce the list of grammar extensions that will be
    applied in the same order and kept synchronized w.r.t. the summary, together
    with a new state. It should be pure. *)

val create_grammar_command : string -> 'a grammar_extension -> 'a grammar_command
(** Create a new grammar-modifying command with the given name. The extension
    function is called to generate the rules for a given data. *)

val extend_grammar_command : 'a grammar_command -> 'a -> unit
(** Extend the grammar of Coq with the given data. *)

(** {6 Extension with parsing entries} *)

type ('a, 'b) entry_command
(** Type of synchronized entry creation. The ['a] type should be
    marshallable. *)

type ('a, 'b) entry_extension = {
  eext_fun : 'a -> GramState.t -> string list * GramState.t;
  eext_eq : 'a -> 'a -> bool;
}
(** Entry extension entry point. Given some ['a] and a current grammar state,
    such a function must produce the list of entry extensions that will be
    created and kept synchronized w.r.t. the summary, together
    with a new state. It should be pure. *)

val create_entry_command : string -> ('a, 'b) entry_extension -> ('a, 'b) entry_command
(** Create a new entry-creating command with the given name. The extension
    function is called to generate the new entries for a given data. *)

val extend_entry_command : ('a, 'b) entry_command -> 'a -> 'b Entry.t list
(** Create new synchronized entries using the provided data. *)

val find_custom_entry : ('a, 'b) entry_command -> string -> 'b Entry.t
(** Find an entry generated by the synchronized system in the current state.
    @raise Not_found if non-existent. *)

(** {6 Protection w.r.t. backtrack} *)

val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

type frozen_t
val parser_summary_tag : frozen_t Summary.Dyn.tag

(** Registering grammars by name *)

val register_grammars_by_name : string -> Entry.any_t list -> unit
val find_grammars_by_name : string -> Entry.any_t list

(** Parsing state handling *)
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit

val get_keyword_state : unit -> CLexer.keyword_state
val set_keyword_state : CLexer.keyword_state -> unit
