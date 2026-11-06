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

val infer : Lam_stats.t -> Lam.t -> unit
(** Infer the arity of the parameters of functions that do not escape the
    compilation unit.

    A function is considered when it is not exported and every occurrence of
    it is the head of an application to at least as many arguments as it has
    parameters. Each of its parameters then gets the arity common to the
    arguments passed at every call site. Passing the parameter itself, in the
    same position, to a recursive call does not constrain it.

    The result is stored as [Lam_id_kind.Parameter arity] in
    [meta.ident_tbl]; parameters without a common known arity are left
    untouched. *)
