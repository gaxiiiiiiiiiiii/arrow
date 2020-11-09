Require Export Relation.

Axiom X : Class.
Axiom N : Class.
Axiom X_ : M X.
Axiom N_ : M N.
Axiom ex_N : exists i, i ∈ N.


Definition Pref R :=
  {: R | fun p => exists x y, M x /\ M y /\ p = <|x,y|> /\ ~ <|y,x|> ∈ R:}.

Definition Ident R :=
  {: R | fun p => exists x y, M x /\ M y /\ p = <|x,y|> /\ <|y,x|> ∈ R:}.  

Definition T :=
  {: Power (X × X) | fun R => Transitive R X /\ Connected R X /\ Reflexive R X :}.  

(* ρ ∈ Tn ρ ≈ (R₁, R₂,...,Rn) *)  
Definition Tn :=
  {: N × T | fun f => f : N → T :}.

Definition Φ :=
  {: Tn × T | fun φ => φ : Tn → T :}.

Axiom Pareto :
  forall φ ρ x y, φ ∈ Φ -> ρ ∈ Tn -> x ∈ X -> y ∈ X ->
  (forall i, i ∈ N -> <|x,y|> ∈ Pref (Value ρ i)) -> <|x,y|> ∈ Pref (Value φ ρ).

Axiom Independence :
  forall f R R' x y, f ∈ Φ -> R ∈ Tn -> R' ∈ Tn -> x ∈ X -> y ∈ X ->
  (forall i, i ∈ N -> 
  (<|x,y|> ∈ Value R i -> <|x,y|> ∈ Value R' i) /\ (<|y,x|> ∈ Value R i -> <|y,x|> ∈ Value R' i)) -> 
  <|x,y|> ∈ Value f R -> <|x,y|> ∈ Value f R'.

Axiom Nondictator :
  forall φ, φ ∈ Φ ->
  ~ exists i, (i ∈ N /\ (forall ρ x y, ρ ∈ Tn -> x ∈ X -> y ∈ X -> <|x,y|> ∈ Value ρ i -> <|x,y|> ∈ Value φ ρ)).

Definition Impossibility := Φ = ∅.

Theorem pref x y R (xX : x ∈ X) (yX : y ∈ X):
  <|x,y|> ∈ Pref R <-> <|x,y|> ∈ R /\ ~ <|y,x|> ∈ R.
Proof.
assert (x_ : M x) by (by exists X).
assert (y_ : M y) by (by exists X).
split => [H | H].
+ apply separation in H.
  induction H.
  apply (conj H).
  induction H0 as [a]; induction H0 as [b].
  induction H0 as [a_]; induction H0 as [b_].
  induction H0 as [xyab notbaR].
  apply (OP_eq x y a b x_ y_ a_ b_) in xyab.
  by induction xyab; subst a b.
+ induction H.
  apply separation.
  apply (conj H).
  by exists x; exists y.
Qed.

Theorem ident x y R (xX : x ∈ X) (yX : y ∈ X):
  <|x,y|> ∈ Ident R <-> <|x,y|> ∈ R /\ <|y,x|> ∈ R.
Proof.
assert (x_ : M x) by (by exists X).
assert (y_ : M y) by (by exists X).
split => [H | H].
+ apply separation in H.
  induction H.
  apply (conj H).
  induction H0 as [a]; induction H0 as [b].
  induction H0 as [a_]; induction H0 as [b_].
  induction H0 as [xyab notbaR].
  apply (OP_eq x y a b x_ y_ a_ b_) in xyab.
  by induction xyab; subst a b.
+ induction H.
  apply separation.
  apply (conj H).
  by exists x; exists y.
Qed.

Theorem pref_ord x y R (xX : x ∈ X) (yX : y ∈ X):
  <|x,y|> ∈ Pref R -> <|x,y|> ∈ R.
Proof.
  rewrite (pref x y R xX yX ).
  intro.
  apply H.
Qed. 

Theorem Ri_ R i :
  R ∈ Tn -> i ∈ N -> M (Value R i).
Proof.
  intros RTn iN. 
  apply separation in RTn.
  induction RTn.
  induction H0.
  induction H1.
  induction H0.
  rewrite <- H1 in iN.
  specialize (value R i H3 iN) as V.
  apply V.
Qed.  


Theorem Ri_T : 
  forall R i, R ∈ Tn -> i ∈ N -> Value R i ∈ T.
Proof.
  intros R i RTn iX.
  apply separation in RTn.
  induction RTn.
  induction H0.
  induction H1.
  induction H0.  
  rewrite <- H1 in iX.
  specialize (value R i H3 iX) as V.
  induction V.
  apply H2.
  apply ran.
  done.
  assert (i_ : Axioms.M i) by (by exists (Dom R)).
  by exists i.
Qed.  

Theorem fR_T :
  forall f R, f ∈ Φ -> R ∈ Tn -> Value f R ∈ T.
Proof.
  intros f R fΦ RTn.
  apply separation in fΦ.
  induction fΦ.
  induction H0.
  induction H0.
  induction H1.
  rewrite <- H1 in RTn.
  specialize (value f R H2 RTn) as v.
  induction v.
  apply H3.
  apply ran.
  done.
  assert (R_ : M R) by (by exists (Dom f)).
  by exists R.
Qed.

Theorem fR_ f R :
  f ∈ Φ -> R ∈ Tn -> M (Value f R).
Proof.
  intros fΦ RTn.
  apply separation in fΦ.
  induction fΦ.
  induction H0.
  induction H0.
  induction H1.
  rewrite <- H1 in RTn.
  specialize (value f R H2 RTn) as v.
  apply v.
Qed.









    

  



