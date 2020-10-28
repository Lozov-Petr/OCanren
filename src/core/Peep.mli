(*
 * OCanren.
 * Copyright (C) 2015-2020
 * Dmitri Boulytchev, Dmitry Kosarev, Alexey Syomin, Evgeny Moiseenko
 * St.Petersburg State University, JetBrains Research
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file COPYING).
 *)

val unification_counter      : unit -> int
val unification_time         : unit -> Mtime.span
val walk_counter             : unit -> int
val conj_counter             : unit -> int
val disj_counter             : unit -> int
val delay_counter            : unit -> int
val unwrap_suspended_counter : unit -> int
val force_counter            : unit -> int
val from_fun_counter         : unit -> int
val bind_counter             : unit -> int
val mplus_counter            : unit -> int
val interleaving_counter     : unit -> int
