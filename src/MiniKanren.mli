(*
 * MiniKanren: miniKanren primitives implementation.
 * Copyright (C) 2015
 * Dmitri Boulytchev, Dmitry Kosarev, St.Petersburg State University
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

(** {1 Implementation of miniKanren primitives} *)

(** {2 Basic modules and types} *)

(** State (needed to perform calculations) *)
module State :
  sig
    (** State type *)
    type t

    (** Printing helper *)
    val show : t -> string
  end

(** Goal converts a state into a lazy stream of states *)
type goal = State.t -> State.t MKStream.t

(** Minikanren integers *)
type int = GT.int

(** Minikanren strings *)
type string = GT.string

(** Minikanren lists *)
type 'a list = 'a GT.list

(** {2 Printing functions} *)

(** Printing helper for minikanren lists (requires state to discover 
    bindings of logical variables) *)
val show_list : State.t -> (State.t -> 'a -> string) -> 'a list -> string

(** Printing helper for minikanren ints (requires state to discover 
    bindings of logical variables) *)
val show_int : State.t -> int -> string

(** Printing helper for minikanren strings (requires state to discover 
    bindings of logical variables) *)
val show_string : State.t -> string -> string

(** {2 miniKanren basic primitives} *)

(** [call_fresh f] creates a fresh logical variable and passes it to the
    parameter *)
val call_fresh : ('a -> State.t -> 'b) -> State.t -> 'b

(** [x === y] creates a goal, which performs a unifications of
    [x] and [y] *)
val (===) : 'a -> 'a -> goal

(** [conj s1 s2] creates a goal, which is a conjunction of its arguments *)
val conj : goal -> goal -> goal

(** [&&&] is left-associative infix synonym for [conj] *)
val (&&&) : goal -> goal -> goal

(** [disj s1 s2] creates a goal, which is a disjunction of its arguments *)
val disj : goal -> goal -> goal

(** [|||] is left-associative infix synonym for [disj] *)
val (|||) : goal -> goal -> goal

(** [?| [s1; s2; ...; sk]] calculates [s1 ||| s2 ||| ... ||| sk] for a
    non-empty list of goals *)
val (?|) : goal list -> goal

(** [conde] is a synonym for [?|] *)
val conde : goal list -> goal

(** [?& [s1; s2; ...; sk]] calculates [s1 &&& s2 && ... &&& sk] for a
    non-empty list of goals *)
val (?&) : goal list -> goal

(** {2 Top-level running primitives} *)

(** [run s] runs a state transformer [s] (not necessarily a goal) in
    initial state *)
val run : (State.t -> 'a) -> 'a

(** [refine s x] refines a logical variable [x] (created with [fresh]) w.r.t.
    state [s] *)
val refine : State.t -> 'a -> 'a

(** [take ?(n=k) s] takes at most [k] first answers from the lazy
    stream [s] (reexported from MKStream for convenience) *)
val take : ?n:int -> State.t MKStream.t -> State.t list
