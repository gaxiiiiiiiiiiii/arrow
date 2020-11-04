Require Export Composition.

Variable N X: Class.
Hypothesis N_ : M N.
Hypothesis X_ : M X.

(* 二項関係全体からなる集合 *)
Definition Rels := Power (X × X).

(* 個人から選考を導く写像（添字付きの二項関係） *)
Definition Rn :=
  {: N × Rels | fun f => f : N → Rels :}.

(* 個人の選好全体から社会的選好を導く写像（アロー型社会厚生関数） *)  
Definition Arrow :=
  {: Rn × Rels | fun f => f : Rn → Rels :}.

(* 二項関係から非対称成分を取り出す演算 *)  
Definition pref R := 
  {: R | fun p => exists x y, M x /\ M y /\ p = <|x,y|> /\ x <> y :}.  

(* 個人の選好の反射性 *)  
Axiom ipref_refl :
  forall i R x, i ∈ N-> R ∈ Rn -> x ∈ X -> 
  <|x,x|> ∈ Value R i.

(* 個人の選好の完備性 *)
Axiom ipref_comp :
  forall i R x y, i ∈ N -> R ∈ Rn -> x ∈ X -> y ∈ X ->
  <|x,y|> ∈ Value R i \/ <|y,x|> ∈ Value R i.

(* 個人の選好の推移性 *)
Axiom ipref_trans :     
  forall i R x y z, i ∈ N -> R ∈ Rn -> x ∈ X -> y ∈ X -> z ∈ X ->
  <|x,y|> ∈ Value R i /\ <|y,z|> ∈ Value R i -> <|x,z|> ∈ Value R i.

(*　社会選好の推移性 *)
Definition spref_trans f (_ : f ∈ Arrow):=
    forall R x y z, R ∈ Rn -> x ∈ X -> y ∈ X -> z ∈ X ->
    <|x,y|> ∈ Value f R /\ <|y,z|> ∈ Value f R -> <|x,z|> ∈ Value f R.

(* 社会選好の準推移性 *)      
Definition spref_quasitrans f (_ : f ∈ Arrow):=
  forall R x y z, R ∈ Rn -> x ∈ X -> y ∈ X -> z ∈ X ->
  <|x,y|> ∈ Value f (pref R) /\ <|y,z|> ∈ Value f (pref R) -> <|x,z|> ∈ Value f (pref R).     

(* 社会選好の非循環性　（清楚的である事と同値？） *)    
Definition spref_acycl f (_ : f ∈ Arrow) :=
    forall M R, R ∈ Rn ->  M ⊆ N -> 
    exists m, m ∈ M /\ (forall n, n ∈ M -> ~ <|n,m|> ∈ Value f R).

(* パレート原理 *)
Definition Pareto f (_ : f ∈ Arrow):=
  forall R i x y, R ∈ Rn -> i ∈ N -> x ∈ X -> y ∈ X ->
  <|x,y|> ∈ Value (pref R) i -> <|x,y|> ∈ Value f (pref R).

(* 独立性 *)    
Definition Independent f (_ : f ∈ Arrow ):=
  forall R R' i x y, R ∈ Rn -> R' ∈ Rn -> i ∈ N -> x ∈ X -> y ∈ X ->
  (<|x,y|> ∈ Value R i <-> <|x,y|> ∈ Value R' i) ->
  (<|x,y|> ∈ Value f R <-> <|x,y|> ∈ Value f R').

(* 非独裁性 *)    
Definition Dictatorial f (_ : f ∈ Arrow) :=
  not (exists i, i ∈ N /\ 
  (forall R x y, R ∈ Rn -> x ∈ X -> y ∈ X ->
   <|x,y|> ∈ Value (pref R) i -> <|x,y|> ∈ Value f (pref R))).

(* 決定的 *)    
Definition Desidable f (_ : f ∈ Arrow)  G (_ : G ⊆ N) :=
    forall R i x y, R ∈ Rn -> i ∈ G -> x ∈ X -> y ∈ X ->
    <|x,y|> ∈ Value (pref R) i -> <|x,y|> ∈ Value f (pref R).


      
Lemma desidable_extend f (fA : f ∈ Arrow) :
  Independent f fA -> Dictatorial f fA -> spref_quasitrans f fA ->
  forall R (RRn : R ∈ Rn) G (GN : G ⊆ N), 
  (exists x y, x ∈ X /\ y ∈ X /\  (forall i, i ∈ G -> <|x,y|> ∈ Value (pref R) i)) ->
  Desidable f fA G GN.
Proof.
  unfold Independent.
  unfold Dictatorial.
  unfold spref_quasitrans.
  unfold Desidable.
  intros HI HD HT R RRn G GN H.
  intros R_ i x_ y_ R_Rn iG x_X y_X xy_Pi.
  induction H as [x]; induction H as [y].
  induction H as [xX]; induction H as [yX].
  specialize (H i iG).
  move : HD.
  rewrite <- allnot_notexists.
  intro.
  specialize (H0 i).
  apply DeMorgan_notand in H0.
  induction H0.
  case (H0 (GN i iG)).
  assert (iN : i ∈ N) by (apply (GN i iG)).
  case (ExcludedMiddle (x = x_)) as [xx_ | notxx_].
  + subst x_.
    case (ExcludedMiddle (y = y_)) as [yy_ | notyy_].
    - subst y_.
      specialize (HI R R_ i x y RRn R_Rn (GN i iG) xX yX).
      case (ExcludedMiddle (x = y)) as [xy | notxy].
      * subst y.
        assert ( <| x, x |> ∈ Value R i <-> <| x, x |> ∈ Value R_ i).
          split => [_ | _].
          by apply ipref_refl.
          by apply ipref_refl.
        specialize (HI H1).



  + move : H0.
    rewrite notall_existsnot.
    intro.
    induction H0 as [R'].
    move : H0.
    rewrite notall_existsnot.
    intro.
    induction H0 as [x'].
    move : H0.
    rewrite notall_existsnot.
    intro.
    induction H0 as [y'].
    




    












    
