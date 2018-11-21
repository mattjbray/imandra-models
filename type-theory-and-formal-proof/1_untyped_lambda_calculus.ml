[@@@redef];;
[@@@max_induct 1i];;
[@@@unroll 35i];;
(** Defn 1.3.2 The set Λ of all λ-terms **)

(** Vars *)

type var =
  { name : string
  ; idx : int (** De Bruijn index for this name *)
  }

let pp_var fmt v =
  let name =
    if v.name = "" then "_" else v.name
  in
  if v.idx = 0 then
    CCFormat.fprintf fmt "%s" name
  else
    CCFormat.fprintf fmt "(%s/%a)" name Z.pp_print v.idx
[@@program];;
[@@@install_printer pp_var];;

let v ?(i=0) x =
  { name = x; idx = i }

let valid_name = function
  | "x" | "y" | "z" -> true
  | _ -> false

let valid_var v =
  v.idx >= 0
  (* un-comment for readable counterexamples *)
  (* && v.idx < 3 && valid_name v.name *)

(** Terms *)

type term =
  | Var of var
  | App of term * term
  | Abs of string * term

let rec pp_term fmt = function
  | Var v -> pp_var fmt v
  | App (m, n) -> CCFormat.fprintf fmt "@[%a@]@[%a@]" pp_term_parens m pp_term_parens n
  | Abs (x, m) -> CCFormat.fprintf fmt "λ%s.@[%a@]" x pp_term m
and pp_term_parens fmt t = match t with
  | App _
  | Abs _
    -> CCFormat.fprintf fmt "(@[%a@])" pp_term t
  | Var _ -> pp_term fmt t
[@@program];;
[@@@install_printer pp_term];;

let var ?i x =
  Var (v ?i x)

let app m n = App (m, n)

let lam x m = Abs (x, m)

let rec valid_term = function
  | Var v -> valid_var v
  | App (m, n) -> valid_term m && valid_term n
  | Abs (x, m) ->
    (* un-comment for readable counterexamples *)
    (* valid_name x && *)
    valid_term m

(** Defn 1.3.5 Multiset of subterms *)
let rec subterms t =
  match t with
  | Var _ -> [t]
  | App (m, n) -> t :: subterms m @ subterms n
  | Abs (_, m) -> t :: subterms m
;;

(** Lemma 1.3.6 *)

(** (1) (Reflexivity) For all λ-terms M, we have M ∈ subterms M*)

theorem subterms_refl m =
  List.mem m (subterms m)
;;

(** (2) (Transitivity) If L ∈ subterms M and M ∈ subterms N, then L ∈ subterms N *)

lemma mem_append_rw x xs ys =
   List.mem x xs || List.mem x ys ==> List.mem x (xs @ ys)
[@@auto][@@rw]
;;

lemma mem_append_fc x xs ys =
   List.mem x (xs @ ys) ==> List.mem x xs || List.mem x ys
[@@auto][@@fc]
;;

theorem subterms_trans l m n =
  List.mem l (subterms m) && List.mem m (subterms n)
  ==>
  List.mem l (subterms n)
[@@auto]
;;

(** Defn 1.3.8 Proper subterm *)

let proper_subterm l m =
  l <> m && List.mem l (subterms m)

(** Defn 1.4.1 FV, the set of free variables of a λ-term *)

let rec free_vars' binder_depths = function
    | Var v ->
      let d = Map.get v.name binder_depths in
      if v.idx >= d then [ { v with idx = v.idx - d } ] else []
    | App (m, n) -> free_vars' binder_depths m @ free_vars' binder_depths n
    | Abs (x, m) -> free_vars' (binder_depths |> Map.add x (Map.get x binder_depths + 1)) m

let free_vars m = free_vars' (Map.const 0) m
;;

free_vars (lam "x" (var "y"));;
free_vars (lam "x" (var "x" ~i:1));;

let rec is_free_var v = function
  | Var u -> v = u
  | App (m, n) -> is_free_var v m || is_free_var v n
  | Abs (x, m) when v.name = x -> is_free_var { v with idx = v.idx + 1} m
  | Abs (_, m) -> is_free_var v m
[@@adm 1i];;

lemma free_vars'_is_free_var binder_depths v m =
  valid_var v && valid_term m &&
  Map.get v.name binder_depths = 0
  ==>
  List.mem v (free_vars' binder_depths m) = is_free_var v m
(* TODO *)
(* [@@auto] *)
;;

(** Defn 1.4.3 Closed λ-term; combinator; Λ⁰ *)

let is_closed m = free_vars m = []

(** Defn 1.6.1 Substitution *)

let rec shift v d =
  function
  | Var u when v.name = u.name ->
    let idx = if u.idx < v.idx then u.idx else u.idx + d in
    Var { u with idx }
  | Var u -> Var u
  | App (m, n) -> App (shift v d m, shift v d n)
  | Abs (y, m) when y = v.name ->
    Abs (y, shift { v with idx = v.idx + 1 } d m)
  | Abs (y, m) ->
    Abs (y, shift v d m)
[@@adm 2i]

let rec substitute x n m =
  match m with
  | Var v when v = x -> n
  | Var v -> Var v
  | App (m', n') ->
    App (substitute x n m', substitute x n n')
  | Abs (y, m') when x.name = y ->
    Abs (y, substitute { x with idx = x.idx + 1 } (shift (v y) 1 n) m')
  | Abs (y, m') ->
    Abs (y, substitute x (shift (v y) 1 n) m')
[@@adm m]
;;

substitute (v "x") (var "y") (lam "y" (var "x"));;

(** Lemma 1.6.5 *)

lemma substitute_non_free_var_is_id x m n =
  not (is_free_var x m)
  ==>
  (m |> substitute x n) = m
[@@auto][@@rw]
;;

theorem substitute_commutes x y m n l =
  valid_var x && valid_var y &&
  valid_term m && valid_term n && valid_term l &&
  x <> y &&
  not (is_free_var x l) ==>
  (m |> substitute x n |> substitute y l)
  =
  (m |> substitute y l |> substitute x (n |> substitute y l))
(* TODO *)
(* [@@auto][@@induct structural m] *)
;;

(** Defn 1.5.2 α-conversion or α-equivalence *)

let rec alpha_eq m n =
  match m, n with
  | Var x, Var y -> x = y
  | App (m, n), App (m', n') -> alpha_eq m m' && alpha_eq n n'
  | Abs (x, m), Abs (y, n) when x = y -> alpha_eq m n
  | Abs (x, m), Abs (y, n) ->
    alpha_eq
      m
      (n
       (* Rename y -> x *)
       |> shift (v x) 1 (* incr all free xs in n *)
       |> substitute (v y) (var x) (* rename all ys bound by this binder to x *)
       |> shift (v y) (-1) (* decr all free ys in n *)
      )
  | _ -> false
;;

theorem alpha_eq_refl m =
  alpha_eq m m
[@@auto][@@rw]
;;

theorem alpha_eq_symmetric m n =
  (* valid_term m && valid_term n ==> *)
  alpha_eq m n = alpha_eq n m
(* TODO *)
(* [@@auto] *)
;;

theorem alpha_eq_transitive m n l =
  (* valid_term m && valid_term n ==> *)
  alpha_eq l m && alpha_eq m n ==> alpha_eq l n
(* TODO *)
(* [@@auto] *)
;;

(** Examples 1.5.3 *)

let ex_1_5_3_1 =
  (app (lam "x" (app (var "x") (lam "z" (app (var "x") (var "y"))))) (var "z"));;
lemma ex_1_5_3_1a =
  alpha_eq ex_1_5_3_1 ex_1_5_3_1;;
lemma ex_1_5_3_1b =
  alpha_eq ex_1_5_3_1
    (app (lam "u" (app (var "u") (lam "z" (app (var "u") (var "y"))))) (var "z"))
[@@simp];;
lemma ex_1_5_3_1c =
  alpha_eq ex_1_5_3_1
    (app (lam "z" (app (var "z") (lam "x" (app (var "z") (var "y"))))) (var "z"))
[@@simp];;
lemma ex_1_5_3_1d =
  not @@ alpha_eq ex_1_5_3_1
  (app (lam "y" (app (var "y") (lam "z" (app (var "y") (var "y"))))) (var "z"))
[@@simp];;
lemma ex_1_5_3_1e =
  not @@ alpha_eq ex_1_5_3_1
  (app (lam "z" (app (var "z") (lam "z" (app (var "z") (var "y"))))) (var "z"))
[@@simp];;
lemma ex_1_5_3_1f =
  not @@ alpha_eq ex_1_5_3_1
  (app (lam "u" (app (var "u") (lam "z" (app (var "u") (var "y"))))) (var "v"))
[@@simp];;

let ex_1_5_3_2 =
  lam "x" (lam "y" (app (app (var "x") (var "z")) (var "y")));;
lemma ex_1_5_3_2a =
  alpha_eq ex_1_5_3_2
    (lam "v" (lam "y" (app (app (var "v") (var "z")) (var "y"))))
[@@simp];;
lemma ex_1_5_3_2b =
  alpha_eq ex_1_5_3_2
    (lam "v" (lam "u" (app (app (var "v") (var "z")) (var "u"))))
[@@simp];;
lemma ex_1_5_3_2c =
  not @@ alpha_eq ex_1_5_3_2
  (lam "y" (lam "y" (app (app (var "y") (var "z")) (var "y"))))
[@@simp];;
lemma ex_1_5_3_2d =
  not @@ alpha_eq ex_1_5_3_2
  (lam "y" (lam "z" (app (app (var "z") (var "z")) (var "y"))))
[@@simp];;

(** Lemma 1.7.1 Let M₁ =α M₂ and N₁ =α N₂. Then also:
    NOTE: typo in the textbook?
*)

(** (1) M₁N₁ =α M₂N₂ *)
theorem lemma_1_7_1_1 m1 n1 m2 n2 =
  alpha_eq m1 m2 && alpha_eq n1 n2
  ==>
  alpha_eq (app m1 n1) (app m2 n2);;

(** (2) λx. M₁ =α λx. M₂ *)
theorem lemma_1_7_1_2 m1 n1 m2 n2 =
  alpha_eq m1 m2 && alpha_eq n1 n2
  ==>
  alpha_eq (lam "x" m1) (lam "x" m2);;

(** (3) M₁[x := N₁] =α M₂[x := N₂] *)
theorem lemma_1_7_1_3 x m1 n1 m2 n2 =
  valid_var x &&
  valid_term m1 &&
  valid_term m2 &&
  valid_term n1 &&
  valid_term n2 &&
  alpha_eq m1 m2 && alpha_eq n1 n2
  ==>
  alpha_eq
    (m1 |> substitute x n1)
    (m2 |> substitute x n2)
(* TODO *)
(* [@@auto] *)
;;

(** Defn 1.8.1 One-step β-reduction, →β *)

let rec beta_reduce_one_step = function
  | App (Abs (x, m), n) ->
    m
    |> substitute (v x) (shift (v x) 1 n)
    |> shift (v x) (-1)
  | Var x -> Var x
  | App (m, n) ->
    (* reduce the lhs first *)
    let m' = beta_reduce_one_step m in
    if m = m' then
      App (m, beta_reduce_one_step n)
    else
      App (m', n)
  | Abs (x, m) -> Abs (x, beta_reduce_one_step m)
;;

(** Examples 1.8.2 *)

lemma shift_up_down x m =
  shift x (-1) (shift x 1 m) = m
[@@auto][@@rw]
;;

lemma ex_1_8_2_1 n =
  (app (lam "x" (app (var "x") (app (var "x") (var "y")))) n |> beta_reduce_one_step) = app n (app n (var "y"))
[@@auto];;
(* Check de Bruijn indices are handled correctly *)
lemma ex_1_8_2_1a n =
  (app (lam "x" (app (var "x") (app (var "x") (var "x" ~i:1)))) n |> beta_reduce_one_step) = app n (app n (var "x"))
[@@auto];;
lemma ex_1_8_2_2 =
  let x, y, z, v = var "x", var "y", var "z", var "v" in
  (app (lam "x" (app (lam "y" (app y x)) z)) v |> beta_reduce_one_step)
  = app (lam "y" (app y v)) z
;;

(** Defn 1.8.3 β-reduction (zero-or-more-step), ↠β *)

let rec beta_reduce k m =
  let m' = beta_reduce_one_step m in
  if m = m' || k < 0 then
    m
  else
    beta_reduce (k-1) m'

(** [beta_reduces_to k n m] is true if [m] ↠β [n] in [i <= k] steps *)
let rec beta_reduces_to ~k n m =
  k >= 0 &&
  (m = n || beta_reduces_to ~k:(k-1) n (beta_reduce_one_step m))
;;

(** Example 1.8.3 (λx.(λy.yx)z)v ↠β zv *)
lemma ex_1_8_3 =
  app (lam "x" (app (lam "y" (app (var "y") (var "x"))) (var "z"))) (var "v")
  |> beta_reduces_to ~k:2 (app (var "z") (var "v"))
;;

(** Lemma 1.8.4 *)

(** (1) ↠β extends →β *)

theorem beta_reduces_to_extends_one_step k m n =
  k >= 1 &&
  beta_reduce_one_step m = n ==>
  m |> beta_reduces_to ~k n
;;

(** (2)(refl) for all M: M ↠β M *)

theorem beta_reduces_to_refl k m =
  k >= 0 ==>
  beta_reduces_to ~k m m
;;

(** (2)(trans) for all L, M and N: if L ↠β M and M ↠β N, then L ↠β N *)

(** lemma: if [m] reduces to [n] in [j] steps, then it also reduces in [k >= j] steps *)
lemma beta_reduces_to_in_more_steps j k m n =
  k >= j &&
  beta_reduces_to j n m
  ==>
  beta_reduces_to k n m
[@@auto][@@fc]
;;

lemma beta_reduces_to_trans_checkpoint j k m n =
  k >= j &&
  beta_reduces_to j n m &&
  m <> n
  ==>
  beta_reduces_to (-1 + k) n (beta_reduce_one_step m)
[@@auto][@@apply beta_reduces_to_in_more_steps j k m n][@@fc]
;;

theorem beta_reduces_to_trans i j k l m n =
  l |> beta_reduces_to ~k:i m &&
  m |> beta_reduces_to ~k:j n &&
  k >= i + j
  ==>
  l |> beta_reduces_to ~k n
[@@auto]
;;
