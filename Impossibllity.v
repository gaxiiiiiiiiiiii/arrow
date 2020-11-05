Require Export Arrow.

Hypothesis Φ0 : Φ <> ∅.
Variable φ : Class.
Hypothesis φΦ :  φ ∈ Φ.

Definition Overriding A r s :=
  A ⊂ N /\ 
    (forall ρ, ρ ∈ Tn -> 
      (forall i, i ∈ A        -> <|r,s|> ∈ Pref (Value ρ i)) -> 
      (forall i, i ∈ (N // A) -> <|s,r|> ∈ Pref (Value ρ i)) ->
     <|r,s|> ∈ Pref (Value φ ρ)).
Notation "A ▷ <| r , s |>" := (Overriding A r s)(at level 10).

Variable x y j J : Class.
Hypothesis JS : J ⊆  X.
Hypothesis xX : x ∈ X.
Hypothesis yX : y ∈ X.
Hypothesis x_ : M x.
Hypothesis y_ : M y.
Hypothesis jJ : j ∈ J.
Hypothesis Jxy : J ▷ <|x,y|>.



Definition K := Single j.
Definition L := J // K.
Definition M := N // J.


Variable z σ : Class.
Hypothesis zX : z ∈ X.
Hypothesis z_ : Axioms.M z.
Hypothesis σTn : σ ∈ Tn.
Hypothesis xyσj : <|x,y|> ∈ Pref (Value σ j).
Hypothesis yzσj : <|y,z|> ∈ Pref (Value σ j).
Hypothesis Lσ : forall l, l ∈ L -> <|z,x|> ∈ Pref (Value σ l) /\ <|x,y|> ∈ Pref (Value σ l).
Hypothesis Mσ : forall m, m ∈ M -> <|y,z|> ∈ Pref (Value σ m) /\ <|z,x|> ∈ Pref (Value σ m).


Theorem pref x y R (x_ : Axioms.M x) (y_ : Axioms.M y):
  <|x,y|> ∈ Pref R <-> <|x,y|> ∈ R /\ ~ <|y,x|> ∈ R.
Proof.
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

Theorem pref_ord x y R (x_ : Axioms.M x) (y_ : Axioms.M y):
  <|x,y|> ∈ Pref R -> <|x,y|> ∈ R.
Proof.
  rewrite (pref x y R x_ y_).
  intro.
  apply H.
Qed.      


Theorem xyJσ :
  forall i, i ∈ J -> <|x,y|> ∈ Pref (Value σ i).
Proof.
  intros i iJ.  
  assert (x_ : Axioms.M x) by (exists X; apply xX).
  assert (y_ : Axioms.M y) by (exists X; apply yX).
  case (ExcludedMiddle (i = j)) as [ij | notij].
  + subst i.
    apply xyσj.
  + assert (i ∈ L).
      apply diff.
      apply (conj iJ).
      intro iK.
      apply in_single in iK.
      case (notij iK).
      by exists J.
      exists J. apply jJ.
    specialize (Lσ i H) as H0.
    apply H0.
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
      

Theorem yxMσ :
  forall i, i ∈ M -> <|y,x|> ∈ Pref (Value σ i).
Proof.
  intros i iM.
  specialize (Mσ i iM) as H.
  induction H.
  apply (pref y z (Value σ i) y_ z_) in H.
  induction H.
  apply (pref z x (Value σ i) z_ x_) in H0.
  induction H0.
  assert (Transitive (Value σ i) X).
    assert (iN : i ∈ N).
      apply diff in iM.
      apply iM.
    specialize (Ri_T σ i σTn iN) as H3.
    apply separation in H3.
    induction H3.
    apply H4.
  specialize (H3 y z x yX zX xX H H0) as H4.
  apply (pref y x (Value σ i) y_ x_).
  apply (conj H4).
  intro.
  apply H1.
  apply (H3 z x y zX xX yX H0 H5).
Qed.

Theorem xyφσ :
  <|x,y|> ∈ Pref (Value φ σ).
Proof.
  induction Jxy.
  apply (H0 σ σTn xyJσ yxMσ).
Qed.





















  
