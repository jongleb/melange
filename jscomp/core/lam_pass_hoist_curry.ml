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

type position = Outside_loop | Inside_loop

type usage =
  | Unused
  | Called of { arity : int; position : position }
      (** every use is the head of an application of unknown arity to
          [arity] arguments *)
  | Escapes

(* The function whose parameters are analysed, when it may call itself. *)
type recursion =
  | Not_recursive
  | Self_recursive of { name : Ident.t; params : Ident.t list }

type redirection =
  | Parameters
  | Parameters_and_recursion of {
      name : Ident.t;
      worker : Ident.t;
      params : Ident.t list;
    }

(* The calls of a parameter that justify normalising it. *)
type normalise_when = Called_anywhere | Called_inside_loop

let hoist_curry =
  let full_call =
    {
      Lam.ap_loc = Location.none;
      ap_inlined = Default_inline;
      ap_status = App_infer_full;
    }
  in
  let usages ~recursion (params : Ident.t list) (body : Lam.t) =
    let usages = Ident.Hashtbl.create 7 in
    List.iter params ~f:(fun param ->
        Ident.Hashtbl.replace usages ~key:param ~data:Unused);
    let note id (usage : usage) =
      match Ident.Hashtbl.find_opt usages id with
      | None -> ()
      | Some previous ->
          Ident.Hashtbl.replace usages ~key:id
            ~data:
              (match (previous, usage) with
              | Unused, usage | usage, Unused -> usage
              | Escapes, _ | _, Escapes -> Escapes
              | Called c1, Called c2 when c1.arity = c2.arity ->
                  Called
                    {
                      arity = c1.arity;
                      position =
                        (match (c1.position, c2.position) with
                        | Inside_loop, _ | _, Inside_loop -> Inside_loop
                        | Outside_loop, Outside_loop -> Outside_loop);
                    }
              | Called _, Called _ -> Escapes)
    in
    let rec visit ~position (lam : Lam.t) =
      match lam with
      | Lvar id | Lmutvar id -> note id Escapes
      | Lapply
          { ap_func = Lvar id; ap_args; ap_info = { ap_status = App_na; _ } }
        when Ident.Hashtbl.mem usages id ->
          let arity = List.length ap_args in
          note id
            (if arity >= 1 && arity <= 8 then Called { arity; position }
             else Escapes);
          List.iter ap_args ~f:(visit ~position)
      | Lapply
          {
            ap_func = Lvar id;
            ap_args;
            ap_info = { ap_status = App_infer_full; _ };
          }
        when Ident.Hashtbl.mem usages id ->
          List.iter ap_args ~f:(visit ~position)
      | Lapply { ap_func = Lvar id; ap_args; _ } -> (
          match recursion with
          | Self_recursive { name; params }
            when Ident.same id name && List.same_length ap_args params ->
              List.iter2 ap_args params ~f:(fun (arg : Lam.t) param ->
                  match arg with
                  | Lvar arg when Ident.same arg param -> ()
                  | arg ->
                      (* the worker could not drop [param] *)
                      note param Escapes;
                      visit ~position arg)
          | Self_recursive _ | Not_recursive ->
              Lam_iter.inner_iter lam ~f:(visit ~position))
      | Lwhile _ | Lfor _ ->
          Lam_iter.inner_iter lam ~f:(visit ~position:Inside_loop)
      | Lletrec (bindings, body)
        when List.exists bindings ~f:(fun (_, binding) ->
                 List.exists bindings ~f:(fun (id, _) ->
                     Lam_hit.hit_variable id binding)) ->
          (* the functions of a recursive group run as many times as it
             recurses *)
          List.iter bindings ~f:(fun (_, (binding : Lam.t)) ->
              match binding with
              | Lfunction { body; _ } -> visit ~position:Inside_loop body
              | binding -> visit ~position binding);
          visit ~position body
      | Lfunction _ -> Lam_iter.inner_iter lam ~f:(visit ~position:Outside_loop)
      | _ -> Lam_iter.inner_iter lam ~f:(visit ~position)
    in
    visit ~position:Outside_loop body;
    usages
  in
  (* [let g' = fun x1 .. xn -> g x1 .. xn], printed as [Curry.__n(g)] *)
  let normalise ~normalised (param, arity) (body : Lam.t) =
    let params =
      List.init ~len:arity ~f:(fun _ -> Ident.create_local "param")
    in
    Lam.let_ StrictOpt
      (Ident.Map.find param normalised)
      (Lam.function_ ~arity ~params ~attr:Lambda.default_function_attribute
         ~body:
           (Lam.apply (Lam.var param)
              (List.map ~f:Lam.var params)
              { full_call with ap_status = App_na }))
      body
  in
  (* Call the normalised parameters directly and, for a worker, turn the
     recursive calls into calls of the worker without the dropped
     arguments. *)
  let rec redirect ~normalised ~redirection (lam : Lam.t) : Lam.t =
    match lam with
    | Lapply { ap_func = Lvar id; ap_args; ap_info = { ap_status = App_na; _ } }
      when Ident.Map.mem id normalised ->
        Lam.apply
          (Lam.var (Ident.Map.find id normalised))
          (List.map ~f:(redirect ~normalised ~redirection) ap_args)
          full_call
    | Lapply { ap_func = Lvar id; ap_args; ap_info } -> (
        match redirection with
        | Parameters_and_recursion { name; worker; params }
          when Ident.same id name ->
            Lam.apply (Lam.var worker)
              (List.filter_map (List.combine params ap_args)
                 ~f:(fun (param, arg) ->
                   if Ident.Map.mem param normalised then None
                   else Some (redirect ~normalised ~redirection arg)))
              { ap_info with ap_status = App_infer_full }
        | Parameters_and_recursion _ | Parameters ->
            Lam.inner_map lam (redirect ~normalised ~redirection))
    | _ -> Lam.inner_map lam (redirect ~normalised ~redirection)
  in
  let called (usages : usage Ident.Hashtbl.t) params ~normalise_when =
    List.filter_map params ~f:(fun param ->
        match (Ident.Hashtbl.find usages param, normalise_when) with
        | Called { arity; position = _ }, Called_anywhere
        | Called { arity; position = Inside_loop }, Called_inside_loop ->
            Some (param, arity)
        | Called { position = Outside_loop; _ }, Called_inside_loop
        | (Unused | Escapes), (Called_anywhere | Called_inside_loop) ->
            None)
  in
  let fresh_names candidates =
    List.fold_left candidates ~init:Ident.Map.empty ~f:(fun acc (param, _) ->
        Ident.Map.add acc ~key:param
          ~data:(Ident.create_local (Ident.name param)))
  in
  let rec transform (lam : Lam.t) : Lam.t =
    match lam with
    | Lletrec
        ([ (name, (Lfunction { params; body; attr; arity } as binding)) ], rest)
      -> (
        let usages =
          usages ~recursion:(Self_recursive { name; params }) params body
        in
        let calls_itself = Lam_hit.hit_variable name body in
        let escapes =
          (* [name] used other than as the head of a full application *)
          let rec escapes (lam : Lam.t) =
            match lam with
            | Lvar id -> Ident.same id name
            | Lapply { ap_func = Lvar id; ap_args; _ }
              when Ident.same id name && List.same_length ap_args params ->
                List.exists ~f:escapes ap_args
            | _ -> Lam_iter.inner_exists lam ~f:escapes
          in
          escapes body
        in
        match called usages params ~normalise_when:Called_anywhere with
        | _ :: _ as candidates
          when calls_itself && (not escapes)
               && List.length candidates < List.length params ->
            let normalised = fresh_names candidates in
            let worker = Ident.create_local (Ident.name name) in
            let kept =
              List.filter params ~f:(fun param ->
                  not (Ident.Map.mem param normalised))
            in
            let worker_params =
              List.map kept ~f:(fun param ->
                  Ident.create_local (Ident.name param))
            in
            let worker_body =
              Lam_subst.subst
                (List.fold_left2 kept worker_params ~init:Ident.Map.empty
                   ~f:(fun acc param worker_param ->
                     Ident.Map.add acc ~key:param ~data:(Lam.var worker_param)))
                (redirect ~normalised
                   ~redirection:
                     (Parameters_and_recursion { name; worker; params })
                   body)
            in
            let wrapper_body =
              List.fold_right candidates
                ~init:
                  (Lam.letrec
                     [
                       ( worker,
                         Lam.function_ ~attr
                           ~arity:(List.length worker_params)
                           ~params:worker_params ~body:(transform worker_body)
                       );
                     ]
                     (Lam.apply (Lam.var worker) (List.map ~f:Lam.var kept)
                        full_call))
                ~f:(normalise ~normalised)
            in
            Lam.letrec
              [ (name, Lam.function_ ~attr ~arity ~params ~body:wrapper_body) ]
              (transform rest)
        | _ :: _ | [] ->
            Lam.letrec [ (name, transform binding) ] (transform rest))
    | Lfunction { params; body; attr; arity } -> (
        let usages = usages ~recursion:Not_recursive params body in
        match called usages params ~normalise_when:Called_inside_loop with
        | [] -> Lam.inner_map lam transform
        | _ :: _ as candidates ->
            let normalised = fresh_names candidates in
            Lam.function_ ~attr ~arity ~params
              ~body:
                (List.fold_right candidates
                   ~init:
                     (transform
                        (redirect ~normalised ~redirection:Parameters body))
                   ~f:(normalise ~normalised)))
    | _ -> Lam.inner_map lam transform
  in
  transform
