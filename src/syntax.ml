(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Printer
open Ppconstr
open Util
open Names
open Constr
open Globnames
open Pp
open Glob_term
open List
open Libnames
open Constrexpr_ops
open Constrexpr
open Evar_kinds
open Equations_common
open Constrintern
open Ltac_plugin

type 'a with_loc = Loc.t * 'a
type identifier = Names.Id.t
   
type generated = bool
(** User-level patterns *)
type user_pat =
    PUVar of identifier * generated
  | PUCstr of constructor * int * user_pats
  | PUInac of Constrexpr.constr_expr
and user_pat_loc = (user_pat, [ `any ]) DAst.t
and user_pats = user_pat_loc list

(** AST *)

type rec_annotation =
  | Nested
  | Struct

type user_rec_annot = (rec_annotation * Id.t with_loc option) option

type rec_arg = int * Id.t with_loc option
    
type rec_annot =
  | StructuralOn of rec_arg
  | NestedOn of rec_arg option

type program_body =
  | ConstrExpr of Constrexpr.constr_expr
  | Constr of EConstr.constr (* We interpret a constr by substituting
                                [Var names] of the lhs bound variables
                                with the proper de Bruijn indices *)

type program =
  (signature * clause list) list

and signature = identifier * rel_context * Constr.t
  
and clause = Loc.t option * lhs * clause rhs
  
and lhs = user_pats

and 'a rhs = 
  | Program of program_body * 'a where_clause list
  | Empty of identifier with_loc
  | Rec of constr_expr * constr_expr option *
             identifier with_loc option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list

and prototype =
  identifier with_loc * user_rec_annot * Constrexpr.local_binder_expr list * Constrexpr.constr_expr

and 'a where_clause = prototype * 'a list

let rec pr_user_loc_pat env ?loc pat =
  match pat with
  | PUVar (i, gen) -> Id.print i ++ if gen then str "#" else mt ()
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
	if not (List.is_empty f) then str "(" ++ pc ++ spc () ++ pr_user_pats env f ++ str ")"
	else pc
  | PUInac c -> str "?(" ++ pr_constr_expr c ++ str ")"

and pr_user_pat env = DAst.with_loc_val (pr_user_loc_pat env)

and pr_user_pats env pats =
  prlist_with_sep spc (pr_user_pat env) pats

let pr_lhs = pr_user_pats

let pplhs lhs = pp (pr_lhs (Global.env ()) lhs)

let rec pr_rhs env = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Rec (t, rel, id, s) -> 
     spc () ++ str "=>" ++ spc () ++ str"rec " ++ pr_constr_expr t ++ spc () ++
       pr_opt (fun (_, id) -> Id.print id) id ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++
                            (match rhs with
                             | ConstrExpr rhs -> pr_constr_expr rhs
                             | Constr c -> str"<constr>") ++
                             pr_wheres env where
  | Refine (rhs, s) -> spc () ++ str "<=" ++ spc () ++ pr_constr_expr rhs ++ 
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")

and pr_wheres env l =
  prlist_with_sep fnl (pr_where env) l
and pr_where env (sign, eqns) =
  pr_proto sign ++ pr_clauses env eqns
and pr_proto ((_,id), _, l, t) =
  Id.print id ++ pr_binders l ++ str" : " ++ pr_constr_expr t
and pr_clause env (loc, lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let ppclause clause =
  pp(pr_clause (Global.env ()) clause)

type pat_expr = 
  | PEApp of qualid Constrexpr.or_by_notation with_loc * pat_expr with_loc list
  | PEWildcard
  | PEInac of constr_expr

type user_pat_expr = pat_expr with_loc

type 'a input_pats =
  | SignPats of 'a
  | RefinePats of 'a list

type pre_equation = 
  constr_expr input_pats * pre_equation rhs

type pre_equations = pre_equation where_clause list

let next_ident_away s ids =
  let n' = Namegen.next_ident_away s !ids in
    ids := Id.Set.add n' !ids; n'

type equation_option = | OInd of bool | ORec of Id.t with_loc option
                       | OComp of bool | OEquations of bool
    
type equation_user_option = equation_option

type equation_options = equation_option list

let pr_r_equation_user_option _prc _prlc _prt l =
  mt ()

let pr_equation_options  _prc _prlc _prt l =
  mt ()

type rec_type = 
  | Structural of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of logical_rec

and logical_rec =
  | LogicalDirect of Id.t with_loc
  | LogicalProj of rec_info

and rec_info = {
  comp : Constant.t option;
  comp_app : Constr.t;
  comp_proj : Constant.t;
  comp_recarg : int;
}

let is_structural = function Some (Structural _) -> true | _ -> false

let is_rec_call sigma r f =
  match r with
  | LogicalProj r -> Equations_common.is_global sigma (ConstRef r.comp_proj) f
  | LogicalDirect (loc, id) -> 
    match EConstr.kind sigma f with
    | Var id' -> Id.equal id id'
    | Const (c, _) ->
      let id' = Label.to_id (Constant.label c) in
      Id.equal id id'
    | _ -> false

let default_loc = Loc.make_loc (0, 0)
         
let is_inaccessible_qualid qid =
  let id = qualid_basename qid in
  Id.equal id (Id.of_string "inaccessible_pattern")

let free_vars_of_constr_expr fid c =
  let rec aux bdvars l = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in
      if Id.List.mem id bdvars then l
      else if Option.cata (Id.equal id) false fid then l
      else
        (try
           match Nametab.locate_extended (Libnames.qualid_of_ident id) with
           | TrueGlobal gr ->
             if not (isConstructRef gr) then Id.Set.add id l
             else l
           | SynDef _ -> l
         with Not_found -> Id.Set.add id l)
    | { CAst.v = CApp ((_, { CAst.v = CRef (qid, _) }), _) }
      when is_inaccessible_qualid qid -> l
    | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Id.Set.empty c

let ids_of_pats id pats =
  fold_left (fun ids p -> Id.Set.union ids (free_vars_of_constr_expr id p))
    Id.Set.empty pats

(* let add_implicits impls avoid pats =
 *   let rec aux l pats =
 *     match l with
 *     | imp :: imps ->
 *        if Impargs.is_status_implicit imp then
 *          let id = Impargs.name_of_implicit imp in
 * 	 let eqf = function ((Some (_, id')), p) -> Id.equal id' id | _ -> false in
 *          (\* try *\) let pat = List.find_map (fun x -> if eqf x then Some (snd x) else None) pats in
 * 	     let pats = List.remove_first eqf pats in
 * 	     pat :: aux imps pats
 *          (\* with Not_found ->
 *           *   let n = next_ident_away id avoid in
 *           *   let pat = PEApp (CAst.make (qualid_of_ident n), []) in
 *           *   avoid := Id.Set.add n !avoid;
 *           *   (default_loc, pat) :: aux imps pats *\)
 *        else begin
 *          match pats with
 * 	 | hd :: tl -> (snd hd) :: aux imps tl
 * 	 | [] -> List.map snd pats
 *        end
 *     | [] -> List.map snd pats
 *   in aux impls pats *)

let chole c loc =
  (* let tac = Genarg.in_gen (Genarg.rawwit Constrarg.wit_tactic) (solve_rec_tac_expr ()) in *)
  let kn = Lib.make_kn c in
  let cst = Names.Constant.make kn kn in
  CAst.make ~loc
  (CHole (Some (ImplicitArg (ConstRef cst, (0,None), false)), Namegen.IntroAnonymous,None)), None

(* let rec interp_pat_expr env ?(avoid = ref Id.Set.empty) (loc, p) =
 *   match p with
 *   | PEApp ((loc, f), l) ->
 *       let r =
 *         try Inl (Smartlocate.smart_global f)
 *         with e -> Inr (PUVar (ident_of_smart_global f, false))
 *       in begin match r with
 *       | Inl (ConstructRef c) ->
 *           let ind, _ = c in
 *           let nparams = Inductiveops.inductive_nparams ind in
 *           let nargs = Inductiveops.constructor_nrealargs c in
 *           let len = List.length l in
 *           let l' =
 *             if len < nargs then List.make (nargs - len) (loc, PEWildcard) @ l
 *             else l
 *           in
 *             Dumpglob.add_glob ~loc (ConstructRef c);
 *             Some loc, PUCstr (c, nparams, List.map (interp_pat_expr env ~avoid) l')
 *       | Inl _ ->
 *           if l != [] then
 *             CErrors.user_err ~loc ~hdr:"interp_pat"
 *                      (str "Pattern variable " ++ pr_smart_global f ++ str " cannot be applied")
 *           else Some loc, PUVar (ident_of_smart_global f, false)
 *       | Inr p -> Some loc, p
 *       end
 *   | PEInac c -> Some loc, PUInac c
 *   | PEWildcard ->
 *       let n = next_ident_away (Id.of_string "wildcard") avoid in
 *         avoid := Id.Set.add n !avoid; Some loc, PUVar (n, true)
 *   (\* | PEPat p ->
 *    *     let ids, pats = intern_pattern env p in
 *    *     let upat =
 *    *       match pats with
 *    *       | [(l, pat)] -> DAst.with_loc_val (translate_cases_pattern env avoid) pat
 *    *       | _ -> user_err_loc (Some loc, "interp_pat",
 *    *                            str "Or patterns not supported by Equations")
 *    *     in upat *\) *)

let check_linearity pats =
  let rec aux ids pats = 
    List.fold_left (fun ids pat ->
      DAst.with_loc_val (fun ?loc pat ->
      match pat with
      | PUVar (n, _) ->
	if Id.Set.mem n ids then
	  CErrors.user_err ?loc ~hdr:"ids_of_pats"
	    (str "Non-linear occurrence of variable in patterns")
	else Id.Set.add n ids
      | PUInac _ -> ids
      | PUCstr (_, _, pats) -> aux ids pats) pat)
      ids pats
  in ignore (aux Id.Set.empty pats)

let pattern_of_glob_constr env avoid gc =
  let rec constructor ?loc c l =
    let ind, _ = c in
    let nparams = Inductiveops.inductive_nparams ind in
    let nargs = Inductiveops.constructor_nrealargs c in
    let l =
      if List.length l < nargs then
        user_err_loc (loc, "pattern_of_glob_constr", str "Constructor is applied to too few arguments")
      else
        if List.length l = nparams + nargs then
          List.skipn nparams l
        else if List.length l = nargs then l
        else
          user_err_loc (loc, "pattern_of_glob_constr", str "Constructor is applied to too many arguments");
    in
    Dumpglob.add_glob ?loc (ConstructRef c);
    PUCstr (c, nparams, List.map (DAst.map_with_loc aux) l)
  and aux ?loc = function
    | GVar id -> PUVar (id, false)
    | GHole (_,_,_) ->
      let n = next_ident_away (Id.of_string "wildcard") avoid in
      avoid := Id.Set.add n !avoid; PUVar (n, true)
    | GRef (ConstructRef cstr,_) -> constructor ?loc cstr []
    | GApp (c, l) ->
      begin match DAst.get c with
        | GRef (ConstructRef cstr,_) -> constructor ?loc cstr l
        | GRef (ConstRef _ as c, _) when GlobRef.equal c (Lazy.force coq_inacc) ->
          let inacc = List.hd (List.tl l) in
          PUInac (Constrextern.extern_glob_constr !avoid inacc)
        | _ -> user_err_loc (loc, "pattern_of_glob_constr", str "Cannot interpret " ++ pr_glob_constr_env env c ++ str " as a constructor")
      end
  (* | GLetIn (Name id as na',b,None,e) when is_gvar id e && na = Anonymous ->
   *    (\* A canonical encoding of aliases *\)
   *    DAst.get (cases_pattern_of_glob_constr na' b) *)
    | _ -> user_err_loc (loc, "pattern_of_glob_constr", str ("Cannot interpret globalized term as a pattern"))
  in DAst.map_with_loc aux gc

let interp_pat env ?(avoid = ref Id.Set.empty) fnid p =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let vars = (Id.Set.elements !avoid) (* (ids_of_pats [p])) *) in
  (* let () = Feedback.msg_debug (str"Variables " ++ prlist_with_sep spc pr_id vars) in *)
  let tys = List.map (fun _ -> EConstr.mkProp) vars in
  let impls = List.map (fun _ -> []) vars in
  let vars, tys, impls =
    match fnid with
    | Some (id, ty, impl) -> (id :: vars, ty :: tys, impl :: impls)
    | None -> (vars, tys, impls)
  in
  (* let () = Feedback.msg_debug (str"Internalizing " ++ pr_constr_expr p) in *)
  let ienv = try compute_internalization_env env sigma Recursive vars tys impls with Not_found ->
    anomaly (str"Building internalization environment")
  in
  let nctx =
    List.map (fun id -> Context.Named.Declaration.LocalAssum (id, Constr.mkProp)) vars
  in
  let env = Environ.push_named_context nctx env in
  let gc =
    try Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~impls:ienv env sigma p
    with Not_found -> anomaly (str"Internalizing pattern")
  in
  try
    match fnid with
    | Some (id, _, _) ->
      DAst.with_loc_val (fun ?loc g ->
          match g with
          | GApp (fn, args) ->
            DAst.with_loc_val (fun ?loc gh ->
                match gh with
                | GVar fid when Id.equal fid id ->
                  let args = List.map (pattern_of_glob_constr env avoid) args in
                  args
                | _ ->
                  user_err_loc (loc, "interp_pats",
                                str "Expecting a pattern for " ++ Id.print id))
              fn
          | _ ->
            user_err_loc (loc, "interp_pats",
                          str "Expecting a pattern for " ++ Id.print id))
        gc
    | None -> [pattern_of_glob_constr env avoid gc]
  with Not_found -> anomaly (str"While translating pattern to glob constr")

let interp_eqn initi is_rec env ty impls eqn =
  let avoid = ref Id.Set.empty in
  let interp_pat = interp_pat env ~avoid in
  let rec aux recinfo i is_rec curpats (pat, rhs) =
    let loc, pats =
      match pat with
      | SignPats pat ->
        avoid := Id.Set.union !avoid (ids_of_pats (Some i) [pat]);
        let loc = Constrexpr_ops.constr_loc pat in
        loc, interp_pat (Some (i, ty, impls)) pat
      | RefinePats pats ->
        avoid := Id.Set.union !avoid (ids_of_pats None pats);
        let loc = Constrexpr_ops.constr_loc (List.hd pats) in
        let pats = List.map (interp_pat None) pats in
        let pats = List.map (fun x -> List.hd x) pats in
        loc, curpats @ pats
    in
    (* Option.iter (fun (loc,id) ->
     *   if not (Id.equal id i) then
     *     user_err_loc (Some loc, "interp_pats",
     *     	     str "Expecting a pattern for " ++ Id.print i);
     *   Dumpglob.dump_reference ~loc "<>" (Id.to_string id) "def")
     *   idopt; *)
    (*   if List.length pats <> List.length sign then *)
    (*     user_err_loc (loc, "interp_pats", *)
    (* 		 str "Patterns do not match the signature " ++  *)
    (* 		   pr_rel_context env sign); *)
    (* let curpats'' = add_implicits impls avoid curpats' in *)
      (* let beginloc = match idopt with
       *   | Some (loc, id) -> Some loc
       *   | _ -> match List.hd curpats' with
       *          | (Some (loc, _), _) -> Some loc
       *          | (None, c) -> Constrexpr_ops.constr_loc c
       * in
       * let endloc = match List.last curpats' with
       *   | (_, c) -> Constrexpr_ops.constr_loc c
       * in
       * match beginloc, endloc with
       * | Some b, Some e -> Some (Loc.merge b e)
       * | Some x, _ -> beginloc
       * | _, _ -> endloc *)
    let curpats' = pats in
    let () = check_linearity pats in
      match is_rec with
      | Some (Structural l) ->
         (* let fnpat = (dummy_loc, PUVar (i, false)) in *)
         let addpat (id, k) =
           match k with
           | NestedOn None when Id.equal id initi -> None
           | _ -> Some (DAst.make (PUVar (id, false)))
         in
         let structpats = List.map_filter addpat l in
         let pats = structpats @ pats in
         (* Feedback.msg_debug (str "Patterns: " ++ pr_user_pats env pats); *)
         (loc, pats,
          interp_rhs recinfo i is_rec curpats' rhs)
      | Some (Logical r) -> 
         (loc, pats, interp_rhs ((i, r) :: recinfo) i is_rec curpats' rhs)
      | None -> (loc, pats, interp_rhs recinfo i is_rec curpats' rhs)
  and interp_rhs recinfo i is_rec curpats = function
    | Refine (c, eqs) -> Refine (CAst.with_loc_val (interp_constr_expr recinfo !avoid) c, 
                                map (aux recinfo i is_rec curpats) eqs)
    | Program (c, w) ->
       let w = interp_wheres recinfo avoid w in
       let c =
         match c with
         | ConstrExpr c -> ConstrExpr (CAst.with_loc_val (interp_constr_expr recinfo !avoid) c)
         | Constr c -> Constr c
       in
       Program (c, w)
    | Empty i -> Empty i
    | Rec (fni, r, id, s) -> 
      let rec_info = LogicalDirect (Option.get (Constrexpr_ops.constr_loc fni), i) in
      let recinfo = (i, rec_info) :: recinfo in
      Rec (fni, r, id, map (aux recinfo i is_rec curpats) s)
    | By (x, s) -> By (x, map (aux recinfo i is_rec curpats) s)
  and interp_wheres recinfo avoid w =
    let interp_where (((loc,id),nested,b,t) as p,eqns) =
      Dumpglob.dump_reference ~loc "<>" (Id.to_string id) "def";
      p, map (aux recinfo id None []) eqns
    in List.map interp_where w
  and interp_constr_expr recinfo ids ?(loc=default_loc) c =
    match c with
    (* |   | CAppExpl of loc * (proj_flag * reference) * constr_expr list *)
    | CApp ((None, { CAst.v = CRef (qid', ie) }), args)
      when qualid_is_ident qid' && List.mem_assoc_f Id.equal (qualid_basename qid') recinfo ->
       let id' = qualid_basename qid' in
       let r = List.assoc_f Id.equal id' recinfo in
       let args =
         List.map (fun (c, expl) -> CAst.with_loc_val (interp_constr_expr recinfo ids) c, expl) args in
       let c = CApp ((None, CAst.(make ~loc (CRef (qid', ie)))), args) in
       let arg = CAst.make ~loc (CApp ((None, CAst.make ~loc c), [chole id' loc])) in
       (match r with
        | LogicalDirect _ -> arg
        | LogicalProj r -> 
          let arg = if Option.is_empty r.comp then [arg, None] else [] in
          let qidproj = Nametab.shortest_qualid_of_global ?loc:qid'.CAst.loc Id.Set.empty (ConstRef r.comp_proj) in
          CAst.make ~loc (CApp ((None, CAst.make ?loc:qid'.CAst.loc (CRef (qidproj, None))),
                                args @ arg)))
    | _ -> map_constr_expr_with_binders Id.Set.add
             (fun ids -> CAst.with_loc_val (interp_constr_expr recinfo ids)) ids (CAst.make ~loc c)
  in aux [] initi is_rec [] eqn
