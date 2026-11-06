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

val hoist_curry : Lam.t -> Lam.t
(** Pay for the arity check of a function-typed parameter once per call of
    its function instead of once per call of the parameter.

    A parameter [g] qualifies when its arity is unknown and every use of it
    is the head of an application to the same number [n] of arguments
    ([1 <= n <= 8]). It is then normalised once with an eta-expansion that
    the printer emits as [Curry.__n(g)], and called directly.

    - In a function whose body calls [g] inside a [for] or [while] loop, the
      normalisation is bound at the start of the body.
    - A self-recursive function that passes [g] unchanged to every recursive
      call is split into a wrapper, with the original name and arity, that
      normalises [g], and a worker without [g] that recurses on itself.

    Must run after the last [Lam_pass_alpha_conversion.alpha_conversion]:
    the applications it creates are already marked as full. *)
