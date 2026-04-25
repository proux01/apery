Definition Sn_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(n + 1 + - m) / ((n + 1 + m)).

Definition Sn (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int), precond.Sn n_ k_ m_ ->
d (int.shift 1 n_) k_ m_ = Sn_cf0_0_0 n_ k_ m_ * d n_ k_ m_.

Definition Sk_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
1.

Definition Sk (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int), precond.Sk n_ k_ m_ ->
d n_ (int.shift 1 k_) m_ = Sk_cf0_0_0 n_ k_ m_ * d n_ k_ m_.

Definition Sm_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(m^3) / (((m + 1) * (n + 1 + m) * (m + - n))).

Definition Sm (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int), precond.Sm n_ k_ m_ ->
d n_ k_ (int.shift 1 m_) = Sm_cf0_0_0 n_ k_ m_ * d n_ k_ m_.

Definition P1_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(2 * k^2 * n + 3 * k^2 + - 2 * k * n^2 + - 3 * k * n + n^3 + 3 * n^2 + 3 * n + 1).

Definition P1_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 1 * (2 * n + 3) * (n^2 + 3 * n + - k * n + k^2 + 3)).

Definition P1_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 1 * k * (2 * n + 3) * (- n + k)).

Definition P1_cf2_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + 2)^3.

Definition P1_cf1_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(k * (2 * n + 3) * (- n + k)).

Definition P1_flat (d : int -> int -> rat) (n_ k_ : int) : rat :=
P1_cf0_0 n_ k_ * d n_ k_ + P1_cf1_0 n_ k_ * d (int.shift 1 n_) k_ + P1_cf0_1 n_ k_ * d n_ (int.shift 1 k_) + P1_cf2_0 n_ k_ * d (int.shift 2 n_) k_ + P1_cf1_1 n_ k_ * d (int.shift 1 n_) (int.shift 1 k_).

Definition P1_seq := [:: [:: P1_cf0_0; P1_cf1_0; P1_cf2_0]; [:: P1_cf0_1; P1_cf1_1]].

Definition P1_horner := punk.biv_horner_seqop2 P1_seq.

Definition Q1_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(2 * (2 * k^2 * n + 3 * k^2 + - 2 * k * n^2 + - 3 * k * n + n^3 + 3 * n^2 + 3 * n + 1) * (- n + - 1 + m) * m) / ((n + 1)^2).

Definition Q1_cf1_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(- 2 * (- n + - 2 + m) * (n + 2) * m).

Definition Q1_cf0_1_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(- 2 * k * (2 * n + 3) * (- n + k) * (- n + - 1 + m) * m) / ((n + 1)^2).

Definition Q1_flat (d : int -> int -> int -> rat) (n_ k_ m_ : int) : rat :=
Q1_cf0_0_0 n_ k_ m_ * d n_ k_ m_ + Q1_cf1_0_0 n_ k_ m_ * d (int.shift 1 n_) k_ m_ + Q1_cf0_1_0 n_ k_ m_ * d n_ (int.shift 1 k_) m_.

(* No definition of constants Q1_seq and Q1_horner: Q1_flat is multivariate. *)

Definition P2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((2 * n + 5) * (n + 1)^3 * (- n + - 1 + k)).

Definition P2_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 1 * (2 * n + 3) * (- 3 * n^4 + k * n^3 + - 22 * n^3 + 5 * k * n^2 + - 62 * n^2 + - 80 * n + 9 * k * n + 7 * k + - 39)).

Definition P2_cf3_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((2 * n + 3) * (n + 3)^3 * (n + k + 3)).

Definition P2_cf2_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 1 * (2 * n + 5) * (3 * n^4 + 26 * n^3 + k * n^3 + 7 * k * n^2 + 86 * n^2 + 17 * k * n + 128 * n + 71 + 13 * k)).

Definition P2_flat (d : int -> int -> rat) (n_ k_ : int) : rat :=
P2_cf0_0 n_ k_ * d n_ k_ + P2_cf1_0 n_ k_ * d (int.shift 1 n_) k_ + P2_cf3_0 n_ k_ * d (int.shift 3 n_) k_ + P2_cf2_0 n_ k_ * d (int.shift 2 n_) k_.

Definition P2_seq := [:: [:: P2_cf0_0; P2_cf1_0; P2_cf2_0; P2_cf3_0]].

Definition P2_horner := punk.biv_horner_seqop2 P2_seq.

Definition Q2_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(2 * m * (- n + - 1 + m) * (2 * n + 5) * (n + 1) * (- n + - 1 + k)).

Definition Q2_cf1_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(- 4 * (- n + - 2 + m) * m * (n + 2) * (- 2 * n^2 + - 8 * n + k + - 7)).

Definition Q2_cf2_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
(- 2 * (- n + - 3 + m) * m * (n + 3) * (2 * n + 3) * (n + k + 3)).

Definition Q2_flat (d : int -> int -> int -> rat) (n_ k_ m_ : int) : rat :=
Q2_cf0_0_0 n_ k_ m_ * d n_ k_ m_ + Q2_cf1_0_0 n_ k_ m_ * d (int.shift 1 n_) k_ m_ + Q2_cf2_0_0 n_ k_ m_ * d (int.shift 2 n_) k_ m_.

(* No definition of constants Q2_seq and Q2_horner: Q2_flat is multivariate. *)

Definition P3_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + - k).

Definition P3_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- n + - 2 + - k).

Definition P3_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- n + k).

Definition P3_cf1_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + 2 + k).

Definition P3_flat (d : int -> int -> rat) (n_ k_ : int) : rat :=
P3_cf0_0 n_ k_ * d n_ k_ + P3_cf1_0 n_ k_ * d (int.shift 1 n_) k_ + P3_cf0_1 n_ k_ * d n_ (int.shift 1 k_) + P3_cf1_1 n_ k_ * d (int.shift 1 n_) (int.shift 1 k_).

Definition P3_seq := [:: [:: P3_cf0_0; P3_cf1_0]; [:: P3_cf0_1; P3_cf1_1]].

Definition P3_horner := punk.biv_horner_seqop2 P3_seq.

Definition Q3_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
0.

Definition Q3_flat (d : int -> int -> int -> rat) (n_ k_ m_ : int) : rat :=
Q3_cf0_0_0 n_ k_ m_ * d n_ k_ m_.

(* No definition of constants Q3_seq and Q3_horner: Q3_flat is multivariate. *)

Definition P4_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(k + 1)^3.

Definition P4_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- 2 * k^3 + - 8 * k^2 + - 11 * k + - 5 + k * n + k * n^2 + 2 * n^2 + 2 * n).

Definition P4_cf0_2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((k + 2) * (n + 2 + k) * (- n + k + 1)).

Definition P4_flat (d : int -> int -> rat) (n_ k_ : int) : rat :=
P4_cf0_0 n_ k_ * d n_ k_ + P4_cf0_1 n_ k_ * d n_ (int.shift 1 k_) + P4_cf0_2 n_ k_ * d n_ (int.shift 2 k_).

Definition P4_seq := [:: [:: P4_cf0_0]; [:: P4_cf0_1]; [:: P4_cf0_2]].

Definition P4_horner := punk.biv_horner_seqop2 P4_seq.

Definition Q4_cf0_0_0 (n_ k_ m_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
let m : rat := m_%:~R in
0.

Definition Q4_flat (d : int -> int -> int -> rat) (n_ k_ m_ : int) : rat :=
Q4_cf0_0_0 n_ k_ m_ * d n_ k_ m_.

(* No definition of constants Q4_seq and Q4_horner: Q4_flat is multivariate. *)


