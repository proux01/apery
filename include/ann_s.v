Require annotated_recs_d.

Definition Sk2_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition Sk2_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition Sk2_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition Sk2_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
1.

Definition Sk2_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
Sk2_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + Sk2_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + Sk2_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + Sk2_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Require annotated_recs_d.

Definition SnSk_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition SnSk_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition SnSk_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
1.

Definition SnSk_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition SnSk_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
SnSk_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + SnSk_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + SnSk_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + SnSk_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Require annotated_recs_d.

Definition Sn2_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + 2 + k).

Definition Sn2_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition Sn2_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(k * (2 * n + 3) * (n + - k)).

Definition Sn2_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
0.

Definition Sn2_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
Sn2_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + Sn2_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + Sn2_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + Sn2_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Definition Sk2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 1 * (k + 1)^3) / (((k + 2) * (n + 2 + k) * (- n + k + 1))).

Definition Sk2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(2 * k^3 + 8 * k^2 + 11 * k + 5 + - k * n + - k * n^2 + - 2 * n^2 + - 2 * n) / (((k + 2) * (n + 2 + k) * (- n + k + 1))).

Definition Sk2 (s : int -> int -> rat) := forall (n_ k_ : int), precond.Sk2 n_ k_ ->
s n_ (int.shift 2 k_) = Sk2_cf0_0 n_ k_ * s n_ k_ + Sk2_cf0_1 n_ k_ * s n_ (int.shift 1 k_).

Definition SnSk_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- n + k) / ((n + 2 + k)).

Definition SnSk_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
1.

Definition SnSk_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + - k) / ((n + 2 + k)).

Definition SnSk (s : int -> int -> rat) := forall (n_ k_ : int), precond.SnSk n_ k_ ->
s (int.shift 1 n_) (int.shift 1 k_) = SnSk_cf0_0 n_ k_ * s n_ k_ + SnSk_cf1_0 n_ k_ * s (int.shift 1 n_) k_ + SnSk_cf0_1 n_ k_ * s n_ (int.shift 1 k_).

Definition Sn2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 2 + - 9 * n^2 + 3 * k * n + - 6 * k^2 + - n^4 + - 5 * n^3 + - 6 * k^3 + - k * n^3 + k * n^2 + 4 * k^2 * n^2 + 2 * k^2 * n + - 4 * k^3 * n + - k + - 7 * n) / (((n + 2)^3 * (n + 2 + k))).

Definition Sn2_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((2 * n + 3) * (n^2 + 3 * n + 3)) / ((n + 2)^3).

Definition Sn2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(2 * k * (2 * n + 3) * (k + 1) * (- n + k)) / (((n + 2)^3 * (n + 2 + k))).

Definition Sn2 (s : int -> int -> rat) := forall (n_ k_ : int), precond.Sn2 n_ k_ ->
s (int.shift 2 n_) k_ = Sn2_cf0_0 n_ k_ * s n_ k_ + Sn2_cf1_0 n_ k_ * s (int.shift 1 n_) k_ + Sn2_cf0_1 n_ k_ * s n_ (int.shift 1 k_).
