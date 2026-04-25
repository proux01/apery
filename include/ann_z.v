Definition Sn2_cf0 (n_ : int) : rat :=
let n : rat := n_%:~R in
(- 1 * (n + 1)^3) / ((n + 2)^3).

Definition Sn2_cf1 (n_ : int) : rat :=
let n : rat := n_%:~R in
((2 * n + 3) * (n^2 + 3 * n + 3)) / ((n + 2)^3).

Definition Sn2 (z : int -> rat) := forall (n_ : int), precond.Sn2 n_ ->
z (int.shift 2 n_) = Sn2_cf0 n_ * z n_ + Sn2_cf1 n_ * z (int.shift 1 n_).
