Goal { Tm · τ  = h0 · Si ̅ ¹ · m }.
etrans.
{
  apply cancel_postcomposition.
  apply (1).
}
etrans.
{
  rewrite assoc'.
  apply cancel_precomposition.
  apply (3).
}
repeat rewrite assoc.
etrans.
{
  do 2 apply cancel_postcomposition.
  apply (2).
}
etrans.
{
  apply cancel_postcomposition.
  rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply (4).
}
repeat rewrite assoc'.
do 2 apply cancel_precomposition.
apply (5).
Qed.
(* ~30 lines *)


