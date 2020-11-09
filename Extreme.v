Require Export Arrow.

Definition max R x:=
  ~ exists y, y ∈ X /\ <|y,x|> ∈ R.

Definition min  R x :=
  ~ exists y, y ∈ X /\ <|x,y|> ∈ R.

Axiom Extreme_ :
  forall f R x, f ∈ Φ -> R ∈ Tn -> x ∈ X ->
  (forall i, i ∈ N -> max (Value R i) x \/ min (Value R i) x )-> 
  forall l s, <|l,x|> ∈ Value f R -> <|x,s|> ∈ Value f R ->
  exists R', R' ∈ Tn /\
  (forall i, i ∈ N -> 
     (max (Value R i) x /\ max (Value R' i) x /\ (forall y, y ∈ X -> ~ <|y,x|> ∈ Ident (Value R' i) ->  <|s,y|> ∈ Pref (Value R' i))) \/
     (min (Value R i) x /\ min (Value R' i) x /\ max (Value R' i) s)
  ).





Theorem Extreme :
  forall f R x, f ∈ Φ -> R ∈ Tn -> x ∈ X ->
  (forall i, i ∈ N -> max (Value R i) x \/ min (Value R i) x )->
  max (Value f R) x \/ min (Value f R) x.
Proof.
  intros f R x fΦ RTn xX H.
  specialize (fR_T f R fΦ RTn) as H0.
  apply separation in H0.
  induction H0 as [fRXX].
  induction H0 as [trans]; induction H0 as [conn refl].



  rewrite /max /min.
  rewrite <- DeMorgan_notand.
  intro.
  induction H0.
  induction H0 as [l]; induction H0 as [lX lxfR].
  induction H1 as [s]; induction H0 as [sX xsfR].
  assert (lsfR : <|l,s|> ∈ Value f R).
    by specialize (trans l x s lX xX sX lxfR xsfR).

  specialize (Extreme_ f R x fΦ RTn xX H l s lxfR xsfR) as H0.
  induction H0 as [R'].
  induction H0 as [R'Tn H'].


  assert (forall i, i ∈ N -> (<|l,x|> ∈ Value R i -> <|l,x|> ∈ Value R' i) /\ (<|x,l|> ∈ Value R i -> <|x,l|> ∈ Value R' i)) as lxInd.
    intros i iN.
    induction (H i iN).
      (* R max *)
      move : H0.
      rewrite /max.
      rewrite <- allnot_notexists.
      intro.
      specialize (H0 l).
      apply DeMorgan_notand in H0.
      induction H0.
      case (H0 lX).
      split => [H1 | H1].
        (* lRx *)
        case (H0 H1).
        (* xRl  *)
        specialize (H' i iN).
        induction H'.
          (* R' max *)
          induction H2.
          induction H3.
          move : H3.
          rewrite /max. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H3 l).
          apply  DeMorgan_notand in H3.
          induction H3.
          case (H3 lX).
          specialize (Ri_T R' i R'Tn iN) as H5.
          apply separation in H5.
          induction H5.
          induction H6.
          induction H7.
          specialize (H7 x l xX lX).
          induction H7.
          done.
          case (H3 H7).
          (* R' min *)
          induction H2.
          induction H3.
          move : H2.
          rewrite /min.
          rewrite <- allnot_notexists.
          intro.
          specialize (H2 l).
          apply DeMorgan_notand in H2.
          induction H2.
          case (H2 lX).
          case (H2 H1).
      (* R min *)
      move : H0.
      rewrite /min.
      rewrite <- allnot_notexists.
      intro.
      specialize (H0 l).
      apply DeMorgan_notand in H0.
      induction H0.
      case (H0 lX).
      split => [H1 | H1].
        (* lx *)
        induction (H' i iN).
          (* R' max *)
          induction H2.
          move : H2.
          rewrite /max. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H2 l).
          apply  DeMorgan_notand in H2.
          induction H2.
          case (H2 lX).
          case (H2 H1).
          (* R' min *)
          induction H2.
          induction H3.
          move : H3.
          rewrite /min. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H3 l).
          apply  DeMorgan_notand in H3.
          induction H3.
          case (H3 lX).
          specialize (Ri_T R' i R'Tn iN) as H5.
          apply separation in H5.
          induction H5.
          induction H6.
          induction H7.
          specialize (H7 x l xX lX).
          induction H7.
          case (H3 H7).
          done.
        (* xl *)
        done.


  assert (forall i, i ∈ N -> (<|x,s|> ∈ Value R i -> <|x,s|> ∈ Value R' i) /\ (<|s,x|> ∈ Value R i -> <|s,x|> ∈ Value R' i)) as xsInd.
    intros i iN.
    induction (H i iN).
      (* R max *)
      move : H0.
      rewrite /max.
      rewrite <- allnot_notexists.
      intro.
      specialize (H0 s).
      apply DeMorgan_notand in H0.
      induction H0.
      case (H0 sX).
      split => [H1 | H1].
        (* sRx *)
        induction (H' i iN).
          (* R' max *)
          induction H2.
          induction H3.
          move : H3.
          rewrite /max. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H3 s).
          apply  DeMorgan_notand in H3.
          induction H3.
          case (H3 sX).
          specialize (Ri_T R' i R'Tn iN) as H5.
          apply separation in H5.
          induction H5.
          induction H6.
          induction H7.
          specialize (H7 x s xX sX).
          induction H7.
          done.
          case (H3 H7).
          (* R' min *)
          induction H2.
          induction H3.
          move : H2.
          rewrite /min.
          rewrite <- allnot_notexists.
          intro.
          specialize (H2 s).
          apply DeMorgan_notand in H2.
          induction H2.
          case (H2 sX).
          case (H2 H1).
        (* xRs *)
        done.
      (* R min *)
      move : H0.
      rewrite /min.
      rewrite <- allnot_notexists.
      intro.
      specialize (H0 s).
      apply DeMorgan_notand in H0.
      induction H0.
      case (H0 sX).
      split => [H1 | H1].
        (* xRs *)
        done.
        (* sRs *)
        induction (H' i iN).
          (* R' max *)
          induction H2.
          move : H2.
          rewrite /max. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H2 s).
          apply  DeMorgan_notand in H2.
          induction H2.
          case (H2 sX).
          case (H2 H1).
          (* R' min *)
          induction H2.
          induction H3.
          move : H3.
          rewrite /min. 
          rewrite <- allnot_notexists.
          intro.
          specialize (H3 s).
          apply  DeMorgan_notand in H3.
          induction H3.
          case (H3 sX).
          specialize (Ri_T R' i R'Tn iN) as H5.
          apply separation in H5.
          induction H5.
          induction H6.
          induction H7.
          specialize (H7 x s xX sX).
          induction H7.
          case (H3 H7).
          done.


  assert (forall i, i ∈ N -> <|s,l|> ∈ Pref (Value R' i)) as slR'i.
    intros i iN.
    specialize (H' i iN).
    specialize (Ri_T R' i R'Tn iN) as H1.
    apply separation in H1.
    induction H1 as [_ H1].
    induction H1 as [_ H1]; induction H1 as [conn' _].
    induction H'.
      (**)
      induction H0 as [_ H0].
      induction H0.
      move : H0.
      rewrite /max.
      rewrite <- allnot_notexists.
      intro.
      specialize (H0 l).
      apply DeMorgan_notand in H0.
      induction H0.
      case (H0 lX).
      assert (~ <|l,x|> ∈ Ident (Value R' i)).
        rewrite (ident l x _ lX xX).
        rewrite DeMorgan_notand.
        apply (or_introl H0).
      by specialize (H1 l lX H2) as slR'j.
      (**)
      induction H0 as [_ H0].
      induction H0.
      move : H1.
      rewrite /max.
      rewrite <- allnot_notexists.      
      intro.
      specialize (H1 l).
      apply DeMorgan_notand in H1.
      induction H1.
      case (H1 lX).      
      specialize (conn' l s lX sX).
      induction conn'.
      case (H1 H2).
      apply (pref s l _ sX lX).
      done.


  specialize (Pareto f R' s l fΦ R'Tn sX lX slR'i) as slfR'.
  specialize (Independence f R R' l x fΦ RTn R'Tn lX xX lxInd lxfR) as lxfR'.
  specialize (Independence f R R' x s fΦ RTn R'Tn xX sX xsInd xsfR) as xsfR'.
  specialize (fR_T f R' fΦ R'Tn) as H0.
  apply separation in H0.
  induction H0 as [_ H0].
  induction H0 as [trans' _].
  assert (lsfR' : <|l,s|> ∈ Value f R').
    by specialize (trans' l x s lX xX sX lxfR' xsfR').
  apply (pref s l (Value f R') sX lX ) in slfR'.
  induction slfR'.
  case (H1 lsfR').
Qed.  

