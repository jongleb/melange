(* Copyright (C) 2015-2016 Bloomberg Finance L.P.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * In addition to the permissions granted to you by the LGPL, you may combine
 * or link a "work that uses the Library" with a publicly distributed version
 * of this file to produce a combined library or application, then distribute
 * that combined work under the terms of your choosing, with no requirement
 * to comply with the obligations normally placed on you by section 4 of the
 * LGPL version 3 (or the corresponding section of a later version of the LGPL
 * should you choose to use a later version).
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. *)

open Import

let collect_info =
  let annotate (meta : Lam_stats.t) (k : Ident.t) (arity : Lam_arity.t) lambda =
    Ident.Hashtbl.replace meta.ident_tbl ~key:k
      ~data:(FunctionId { arity; lambda })
  in
  let add_parameters (meta : Lam_stats.t) params =
    List.iter params ~f:(fun p ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:p
          ~data:(Parameter Lam_arity.na))
  in
  let functor_result (lam : Lam.t) =
    match lam with
    | Lapply
        {
          ap_func =
            Lprim
              {
                primitive = Pfield (_, Fld_module { name });
                args = [ Lglobal_module { id; dynamic_import } ];
                _;
              };
          ap_args;
          _;
        } -> (
        match
          Lam_compile_env.query_external_id_info ~dynamic_import id name
        with
        | Some { arity = Functor { arity = Arity_info ([ n ], _); result }; _ }
          when List.length ap_args = n ->
            Some
              (Array.map result ~f:(fun arity ->
                   Lam_id_kind.Element.Arity arity))
        | Some { arity = Single _ | Submodule _ | Functor _; _ } | None -> None)
    | _ -> None
  in
  let rec field_of_shape (meta : Lam_stats.t) (shape : Lam.Constant.t)
      (element : Lam_id_kind.Element.t) : Lam_id_kind.Element.t =
    match (shape, element) with
    | ( Const_int { comment = Pt_recursive_module_shape Function; _ },
        ((Arity _ | SimpleForm _) as element) ) ->
        Arity (Lam_arity_analysis.arity_of_element meta element)
    | ( Const_block
          (_, Blk_constructor _, [ Const_block (_, Blk_array, components) ]),
        _ ) -> (
        match Lam_stats.elements_of_element meta element with
        | Some elements when List.length components = Array.length elements ->
            Block
              (Array.map2 (Array.of_list components) elements
                 ~f:(fun (component : Lam.Constant.t) element ->
                   match component with
                   | Const_block (_, Blk_tuple, [ shape; Const_string _ ]) ->
                       field_of_shape meta shape element
                   | _ -> NA))
        | Some _ | None -> NA)
    | _ -> NA
  in
  let rec collect_bind (meta : Lam_stats.t) rec_flag
      (mutability : Asttypes.mutable_flag) (ident : Ident.t) (lam : Lam.t) =
    match lam with
    | Lconst v ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident ~data:(Constant v)
    (* *)
    | Lprim { primitive = Pmakeblock (_, _, Immutable); args = ls; _ } ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:(Lam_id_kind.of_lambda_block ls);
        List.iter ~f:(collect meta) ls
    | Lprim { primitive = Psome | Psome_not_nest; args = [ v ]; _ } ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:(Normal_optional v);
        collect meta v
    | Lprim
        {
          primitive =
            Praw_js_code { code_info = Exp (Js_function { arity; _ }); _ };
          args = _;
          _;
        } ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:
            (FunctionId
               { arity = Lam_arity.info [ arity ] false; lambda = None })
    | Lprim { primitive = Pnull_to_opt; args = [ (Lvar _ as l) ]; _ } ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:(OptionalBlock (l, Null))
    | Lprim { primitive = Pundefined_to_opt; args = [ (Lvar _ as l) ]; _ } ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:(OptionalBlock (l, Undefined))
    | Lprim { primitive = Pnull_undefined_to_opt; args = [ (Lvar _ as l) ]; _ }
      ->
        Ident.Hashtbl.replace meta.ident_tbl ~key:ident
          ~data:(OptionalBlock (l, Null_undefined))
    | Lglobal_module { id = v; _ } ->
        Lam_util.alias_ident_or_global meta ident v (Module v)
    | Lvar v ->
        (* if Ident.global v then  *)
        Lam_util.alias_ident_or_global meta ident v NA
        (* enven for not subsitution, it still propogate some properties *)
        (* else () *)
    | Lfunction { params; body; _ }
    (* TODO record parameters ident ?, but it will be broken after inlining *)
      ->
        (* TODO could be optimized in one pass?
            -- since collect meta would iter everywhere,
            so -- it would still iterate internally
        *)
        add_parameters meta params;
        let arity = Lam_arity_analysis.get_arity meta lam in
        annotate meta ident arity (Some (lam, rec_flag));
        collect meta body
    | x -> (
        collect meta x;
        let is_export_id = Ident.Set.mem ident meta.export_idents in
        match mutability with
        | Mutable ->
            (* a later [Lassign] may change the arity *)
            if is_export_id then
              annotate meta ident (Lam_arity_analysis.get_arity meta x) None
        | Immutable -> (
            match functor_result x with
            | Some fields ->
                Ident.Hashtbl.replace meta.ident_tbl ~key:ident
                  ~data:(ImmutableBlock fields)
            | None ->
                let arity = Lam_arity_analysis.get_arity meta x in
                if is_export_id || not (Lam_arity.first_arity_na arity) then
                  annotate meta ident arity None))
  and collect meta (lam : Lam.t) =
    match lam with
    | Lfunction { params; body = l; _ } ->
        (* functor ? *)
        add_parameters meta params;
        collect meta l
    | Llet (_, ident, arg, body) ->
        collect_bind meta Lam_non_rec Immutable ident arg;
        collect meta body
    | Lmutlet (ident, arg, body) ->
        collect_bind meta Lam_non_rec Mutable ident arg;
        collect meta body
    | Lletrec (bindings, body) ->
        (match bindings with
        | [ (ident, arg) ] -> collect_bind meta Lam_self_rec Immutable ident arg
        | _ ->
            List.iter
              ~f:(fun (ident, arg) ->
                collect_bind meta Lam_rec Immutable ident arg)
              bindings);
        collect meta body
    | Lprim
        { primitive = Pupdate_mod; args = [ Lconst shape; Lvar m; value ]; _ }
      -> (
        collect meta value;
        let result = Lam.result_expression value in
        let element =
          match functor_result result with
          | Some fields -> Lam_id_kind.Element.Block fields
          | None -> Lam_id_kind.Element.of_lambda result
        in
        match field_of_shape meta shape element with
        | Block fields ->
            Ident.Hashtbl.replace meta.ident_tbl ~key:m
              ~data:(ImmutableBlock fields)
        | NA | SimpleForm _ | Arity _ -> ())
    | lam -> Lam_iter.inner_iter lam ~f:(collect meta)
  in
  fun (meta : Lam_stats.t) (lam : Lam.t) -> collect meta lam
