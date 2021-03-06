(*
 * OCanren.
 * Copyright (C) 2015-2017
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

open Logic
open Core

@type 'a logic'                = 'a logic                                   with show, gmap, html, eq, compare, foldl, foldr

let logic' = logic;;

@type ('a, 'b) ground          = 'a * 'b                                    with show, gmap, html, eq, compare, foldl, foldr
@type ('a, 'b) logic           = ('a * 'b) logic'                           with show, gmap, html, eq, compare, foldl, foldr

type ('a, 'b, 'c, 'd) groundi = (('a, 'c) ground, ('b, 'd) logic) injected 

let logic = {
  logic with
  GT.plugins =
    object(this)
      method compare       = logic.GT.plugins#compare
      method gmap          = logic.GT.plugins#gmap
      method eq            = logic.GT.plugins#eq
      method foldl         = logic.GT.plugins#foldl
      method foldr         = logic.GT.plugins#foldr
      method html          = logic.GT.plugins#html
      method show    fa fb = GT.show(logic') (fun l -> GT.show(GT.pair) fa fb l)
    end
} 

let inj f g p = to_logic (GT.(gmap pair) f g p)

module T =
  struct
    @type ('a, 'b) t = 'a * 'b with show, gmap, html, eq, compare, foldl, foldr
    let fmap f g x = GT.(gmap pair) f g x
  end

include T
include Fmap2 (T)

let pair x y = Logic.inj @@ distrib (x, y)
