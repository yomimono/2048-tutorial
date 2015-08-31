(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the BSD2 License.
 * See the file COPYING for details.
 *)

let () = Random.self_init () (* get a seed for random numbers *)

(** Squares and tiles *)

(* The provenance of a square is a list of the previous positions and
   values of the current occupants.

   A freshly-populated square has provenance
     [].

   A square unchanged by the last move has provenance
     [{shift = 0; value = v}].

   A square occupied by a shifted tile has provenance
     [{shift = s; value = v}].

   A square occupied by combining two tiles has provenance
     [{shift = s1; value = v}; {shift = s2; value = v}].
*)
type provenance = { shift : int; value : int }

(* A tile is represented as its value. *)
type tile = int * provenance list

(* An unoccupied square is represented as None.
   A square occupied by a tile t is represented as Some t. *)
type square = tile option

(* A board is a list of lists of squares *)
type row = square list
type board = row list

type move = L | R | U | D

module type Solution = sig
  val is_square_2048: square -> bool
  val is_complete_row: row -> bool
  val is_board_winning : board -> bool
  val insert_square : square -> board -> board option
  val shift_left_helper: row -> row -> row
  val shift_board : move -> board -> board
  val shift_board_honestly : move -> board -> (board * bool)
  val is_game_over : board -> bool
  val square_provenances: square -> provenance list
end

let empty = None
let t2 = Some (2, [])
let t4 = Some (4, [])
let t8 = Some (8, [])
let t16 = Some (16, [])
let t32 = Some (32, [])
let t64 = Some (64, [])
let t128 = Some (128, [])
let t256 = Some (256, [])
let t512 = Some (512, [])
let t1024 = Some (1024, [])
let t2048 = Some (2048, [])

(* The value of the occupant of a square, if the square is occupied. *)
let square_value (sq : square) = match sq with
| None -> None
| Some (x, _) -> Some x


let string_of_square = function
| Some (s, _) -> string_of_int s
| None -> " "

(* Select a tile to insert.  Returns t4 10% of the time and t2 90% of the time. *)
let new_square () : square =
  match Random.int 10 with
  | 0 -> t4
  | _ -> t2

(** Boards *)

let create_board () =
  [ [empty; t2   ; empty; empty];
    [empty; empty; empty; empty];
    [empty; empty; empty; empty];
    [empty; empty; empty; t2   ]; ]

let board_size = Utils.listlist_dims
let fold_board = Utils.fold_listlisti

(** Moves *)

module Make (S: Solution) = struct

  include S

  (** High-level interface. *)
  let game_move (mv : move) (b : board) : board =
    match S.shift_board_honestly mv b with
    | b, false -> b
    | b', true ->
        match S.insert_square (new_square ()) b' with
        | None -> b'
        | Some b'' -> b''

end

module Default = struct

  (********* Step 1 *********)

  (* Your first task is to fix the code so that the tests pass. *)

  let is_square_2048 (sq : square) = match sq with
  | Some (2048, _) -> true
  | _ -> false

  let is_board_winning (b : board) =
    let is_winning_row row = List.exists is_square_2048 row in
    List.exists is_winning_row b

  (* At this point you should be able to run the tests again to check
     that your implementation is correct. *)

  (********* Step 2 *********)

  (* The next step is to implement the logic for sliding boards up,
     down, left and right. *)

  let rec shift_left_helper (r : row) (empties : row) : row =
    let increment_shift prov : provenance =
      { shift = prov.shift + 1; value = prov.value }
    in
    let increment_shifts (sq : square) =
      match sq with
      | None -> None
      | Some (x, prov) -> Some (x, List.map increment_shift prov)
    in
    match r with
    | [] -> empties
    | None :: r ->
        (* increment the shift levels of all entries in r by 1 *)
        shift_left_helper (List.map increment_shifts r) (empties @ [None])
    | (Some (x, left_prov)) :: (Some (y, right_prov)) :: r when x = y ->
        let plist : provenance list =
          (* left tile doesn't shift - it's already maximally left *)
          [{shift = (List.hd left_prov).shift; value = x}; 
             {shift = (List.hd right_prov).shift + 1; value = y}; ] in
        let new_tile : (int * provenance list) option =
          Some (x+y, plist) in
        let right = shift_left_helper (None::r) [] in
        new_tile :: right @ empties
    | Some thing :: None :: r ->
        shift_left_helper (Some thing::(List.map increment_shifts r))
          (empties @ [None] : row)
    | Some thing :: r ->
        let right = shift_left_helper r [] in
        (Some thing) :: right @ empties

  let clear_provenance tile = match tile with
  | None -> None
  | Some (x, _) -> Some (x, [{shift = 0; value = x}])

  let shift_left (r : row) =
    shift_left_helper (List.map clear_provenance r) []
  let shift_right (r : row) = List.rev (shift_left_helper (List.rev (List.map
                                                                       clear_provenance
                                                                       r)) [])

  (* Shift a row in the specified direction according to the rules of the game. *)
  let shift_board (mv : move) (b : board) : board =
    match mv with
    | L -> List.map shift_left b
    | R -> List.map shift_right b
    | U -> Utils.transpose (List.map shift_left (Utils.transpose b))
    | D -> Utils.transpose (List.map shift_right (Utils.transpose b))

  (* disallow moves that don't change the board *)
  let shift_board_honestly mv (board : board) : (board * bool)=
    let tiles_equal (v1, _) (v2, _) = v1 = v2 in
    let squares_equal s1 s2 = match s1, s2 with
    | None, None -> true
    | Some x, Some y when tiles_equal x y -> true
    | _, _ -> false
    in
    let rows_equal r1 r2 =
      (List.length r1 = List.length r2) && List.for_all2 squares_equal r1 r2 in
    let boards_equal b1 b2 = List.for_all2 rows_equal b1 b2 in
    let new_board = shift_board mv board in
    if boards_equal new_board board
    then (List.map (List.map clear_provenance) board, false)
    else (new_board, true)

  (********* Step 3 *********)

  (* The next step is to implement a function for adding new tiles to
     the board after a move. *)
  let insert_square (sq : square) (b : board) : board option =
    let has_empty row = List.exists ((=) None) row in
    let rec randomize_empty row =
      if has_empty row then begin
        let index = Random.int (List.length row) in
        match List.nth row index with
        | None -> Some (Utils.replace_at index (fun _ -> sq) row)
        | Some x -> randomize_empty row
      end else
      None
    in
    let rec randomize_random_row rows =
      let index = Random.int (List.length rows) in
      match randomize_empty (List.nth rows index) with
      | None -> randomize_random_row rows
      | Some randomized_row ->
          Some (List.mapi (fun i original_row ->
              if i = index then randomized_row else original_row) rows)
    in
    match b with
    | [] -> None
    | rows ->
        match List.filter has_empty rows with
        | [] -> None
        | rows ->
            randomize_random_row b

  (* There's a minor milestone at this point: if the tests pass then
     the game should be somewhat playable.  (The sliding animations
     won't appear until you've completed step 5.)  You can try out the
     game by loading `2048/_build/src/2048.html` in a browser. *)

  (********* Step 4 *********)

  (* You've written have a check for a winning board, but we don't yet
     have a way to check whether the game has been lost.  The game is
     lost when it's no longer possible to make a move. *)

  let is_complete_row (r : row) : bool =
    let has_empty row = List.exists ((=) None) row in
    match has_empty r with
    | true -> false
    | false -> not
                 (has_empty (shift_left r) ||
                  has_empty (shift_right r))

  let is_game_over (b : board) =
    let check_board rows = List.for_all (fun r -> is_complete_row r) rows in
    match b with
    | [] -> true
    | board -> check_board board && check_board (Utils.transpose board)

  (********* Step 5 *********)

  (* At this point it's possible to play the game, but the tiles leap
     disconcertingly around the board rather than sliding smoothly.
     Sliding animations require keeping track of where tiles came
     from: their *provenance*. *)

  (* TODO: Change the definition of the `tile` type in `g2048.ml` to
     include provenance: {| type tile = int * provenance list |}

     You'll need to reorder the type definitions so that `provenance`
     is defined before `tile`.  *)
  let square_provenances (sq : square ) =
    match sq with
    | None -> []
    | Some (tile, provenances) -> provenances

  (* TODO: Update the shift functions (`shift_left` etc.) to keep
     track of provenance. *)

  (* Once the provenance tests pass you can run the game again and see
     the sliding animations in action! *)

  (********* Step 6: Roll the Dice  *********)

  (* Always inserting squares in the first empty space makes the game
     much less challenging.  See if you can update `insert_square` to
     use a random empty position instead (perhaps using
     `Utils.replace_at`).  Don't forget to check that the tests still
     pass! *)

end
