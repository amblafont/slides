Goal { Tm · τ  = h0 · Si ̅ ¹ · m }.

assert(eq : { Tm = TSi · Tσ }).
{ admit. }
etrans.
{
  apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { Tσ · τ  = hx · Sτ · σ }).
{ admit. }
etrans.
{
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { TSi · hx = h0 · STi }).
{ admit. }
etrans.
{
  do 2 apply cancel_postcomposition.
  apply eq.
}
...

asert(eq : { STi · Sτ = Si ̅ ¹ · Si }).
{ admit. }
etrans.
{
  apply cancel_postcomposition.
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
assert(eq : { Si · σ = m }).
{ admit. }
etrans.
{
  repeat rewrite assoc'.
  do 2 apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
 apply idpath.
Qed.


