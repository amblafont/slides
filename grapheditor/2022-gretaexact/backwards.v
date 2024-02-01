etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  (* remove this after copying the goal *)
  duplicate_goal.
  admit.
  (* copy the result in the proof editor *)
  norm_graph.
  admit.
}
repeat rewrite assoc.


