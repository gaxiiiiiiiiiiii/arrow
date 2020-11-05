Require Export Composition.



Definition Transitive R S :=
    forall x y z, x ∈ S -> y ∈ S -> z ∈ S -> 
    <|x,y|> ∈ R -> <|y,z|> ∈ R -> <|x,z|> ∈ R.

Definition Symmetric R S :=
  forall x y, x ∈ S -> y ∈ S -> 
  <|x,y|> ∈  R -> <|y,x|> ∈ R.
      
Definition Antisymmetric R S :=
  forall x y, x ∈ S -> y ∈ S -> 
  <|x,y|> ∈ R -> <|y,x|> ∈ R -> x = y.

Definition Asymmetric R S :=
  forall x y, x ∈ S -> y ∈ S -> 
  <|x,y|> ∈ R -> ~ <|y,x|> ∈ R.

Definition Nonsymmetric R S :=
  ~ Symmetric R S /\ ~ Antisymmetric R S.
  
Definition Connected R S :=
  forall x y, x ∈ S -> y ∈ S -> <|x,y|> ∈ R \/ <|y,x|> ∈ R.

Definition Reflexive R S :=
  forall x, x ∈ S -> <|x,x|> ∈ R.

Definition Irreflexive R S :=
  forall x, x ∈ S -> ~ <|x,x|> ∈ R.

Definition Nonreflexive R S :=
  exists x y, x ∈ S /\ y ∈ S /\ <|x,x|> ∈ R /\ ~ <|y,y|> ∈ R.

Theorem asym_irr R S :
    Asymmetric R S -> Irreflexive R S.
Proof.
  intros H x xS xxR.
  specialize (H x x xS xS xxR).
  case (H xxR).
Qed.

Theorem transirr_asym R S :
  Transitive R S -> Irreflexive R S -> Asymmetric R S.
Proof.
  intros trans irr x y xS yS xyR yxR.
  specialize (trans x y x xS yS xS xyR yxR).
  specialize (irr x xS).
  case (irr trans).
Qed.

Definition Tiering R S :=
  Transitive R S /\ Nonsymmetric R S.

Definition Preordering R S :=
    Transitive R S /\ Reflexive R S.

    




      


        

