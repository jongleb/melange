(* Copyright (C) 2026 Melange contributors
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

let infer =
  (* For every parameter of a non-escaping function, the arguments passed to
     it, one per call site. *)
  let parameter_arguments (meta : Lam_stats.t) (lam : Lam.t) =
    let functions = Ident.Hashtbl.create 17 in
    let call_sites = Ident.Hashtbl.create 17 in
    let escaped = Ident.Hashtbl.create 17 in
    let bind id (arg : Lam.t) =
      match arg with
      | Lfunction { params = _ :: _ as params; _ } ->
          Ident.Hashtbl.replace functions ~key:id ~data:params
      | _ -> ()
    in
    let rec visit (lam : Lam.t) =
      match lam with
      | Lvar id | Lmutvar id -> Ident.Hashtbl.replace escaped ~key:id ~data:()
      | Lapply { ap_func = Lvar id; ap_args; _ } ->
          Ident.Hashtbl.replace call_sites ~key:id
            ~data:
              (ap_args :: Ident.Hashtbl.find_default call_sites id ~default:[]);
          List.iter ~f:visit ap_args
      | Llet (_, id, arg, _) ->
          bind id arg;
          Lam_iter.inner_iter lam ~f:visit
      | Lletrec (bindings, _) ->
          List.iter ~f:(fun (id, arg) -> bind id arg) bindings;
          Lam_iter.inner_iter lam ~f:visit
      | _ -> Lam_iter.inner_iter lam ~f:visit
    in
    visit lam;
    Ident.Hashtbl.fold functions ~init:[] ~f:(fun ~key:id ~data:params acc ->
        let arity = List.length params in
        match Ident.Hashtbl.find_opt call_sites id with
        | Some (_ :: _ as sites)
          when (not (Ident.Hashtbl.mem escaped id))
               && (not (Ident.Set.mem id meta.export_idents))
               && List.for_all sites ~f:(fun args -> List.length args >= arity)
          ->
            let sites =
              List.map sites ~f:(fun args -> fst (List.split_at args arity))
            in
            List.fold_left
              ~f:(fun acc (index, param) ->
                (param, List.map sites ~f:(fun args -> List.nth args index))
                :: acc)
              ~init:acc
              (List.mapi params ~f:(fun index param -> (index, param)))
        | Some _ | None -> acc)
  in
  let arity_of_arguments (meta : Lam_stats.t) param (args : Lam.t list) =
    List.fold_left args ~init:None ~f:(fun acc (arg : Lam.t) ->
        match arg with
        | Lvar id when Ident.same id param -> acc
        | arg -> (
            let arity = Lam_arity_analysis.get_arity meta arg in
            match acc with
            | None -> Some arity
            | Some acc -> Some (Lam_arity.join acc arity)))
  in
  (* A parameter whose arguments mention parameters of other functions is
     resolved once those are; iterate until nothing changes. A resolved
     arity never changes later: it was computed from arguments that were all
     known already. *)
  let rec resolve (meta : Lam_stats.t) pending =
    let resolved, pending =
      List.partition_map pending ~f:(fun ((param, args) as entry) ->
          match arity_of_arguments meta param args with
          | Some (Arity_info (_ :: _, _) as arity) -> Left (param, arity)
          | Some (Arity_na | Arity_info ([], _)) | None -> Right entry)
    in
    match resolved with
    | [] -> ()
    | _ :: _ ->
        List.iter resolved ~f:(fun (param, arity) ->
            Ident.Hashtbl.replace meta.ident_tbl ~key:param
              ~data:(Parameter arity));
        resolve meta pending
  in
  fun (meta : Lam_stats.t) (lam : Lam.t) ->
    resolve meta (parameter_arguments meta lam)
