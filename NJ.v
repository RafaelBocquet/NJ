Require Import Arith.
Require Import Lists.List.
Require Import Coq.Relations.Relations.
Require Coq.Vectors.Vector.
Import Vector.VectorNotations.
Require Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Structures.Orders.
Require Import Program.

Hint Immediate eq_nat_dec.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
    | H : _ |- _ => solve [ inversion H; subst; t ]
  end
    || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

Theorem Forall_app : forall A (R : A -> Prop) l1 l2,
                       Forall R l1 -> Forall R l2 -> Forall R (l1 ++ l2).
Proof.
  induction l1; simpl; intros.
  auto.
  inversion H; constructor; auto.
Qed.

Notation "'sigma' x .. y ',' p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
                                     (at level 180, x binder, right associativity)
                                   : type_scope.

Lemma fin_case :
  forall n (P : Fin.t (S n) -> Type),
    (P Fin.F1) ->
    (forall x, P (Fin.FS x)) ->
    (forall x, P x).
Proof.
  intros.
  refine (match x as x' in Fin.t n'
                return forall pf : n' = S n,
                         eq_rect n' Fin.t x' (S n) pf = x ->
                         P x with
            | Fin.F1 _ => _
            | Fin.FS _ _ => _
          end eq_refl _).
  - intros.
    inversion pf.
    subst.
    rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
    auto.
  - intros.
    inversion pf.
    subst.
    rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
    auto.
  - rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
    reflexivity.
Qed.

Ltac fin_dep_destruct v :=
  pattern v; apply fin_case; clear v; intros.

Ltac finite :=
  let rec finite' n x :=
      match n with
        | S ?n_ =>
          let x' := fresh "x" in
          pattern x; apply fin_case; [clear x | clear x; intros x'; finite' n_ x']
        | O => pattern x; apply Fin.case0
      end
  in
  match goal with
    | [ |- forall (x : Fin.t ?n), _ ] =>
      intros x; finite' n x
  end.

Lemma eq_fin_dec : forall {n} (f f' : Fin.t n), {f = f'} + {f <> f'}.
Proof.
  induction n; intros.
  apply Fin.case0; auto.
  fin_dep_destruct f; fin_dep_destruct f';
  try (right; intro; solve by inversion).
  left; auto.
  specialize (IHn x x0).
  destruct IHn.
  left; f_equal; auto.
  right. intro. inversion H. apply inj_pair2_eq_dec in H1. auto. auto.
Qed.

Hint Immediate eq_fin_dec.

Lemma eq_vector_dec_ind : forall {n A} (v v' : Vector.t A n), (forall i t, {v[@i] = t} + {v[@i] <> t}) -> {v = v'} + {v <> v'}.
Proof.
  induction n; dependent destruction v; dependent destruction v'; intros.
  left; auto.
  assert (forall (i : Fin.t n) (t : A), {v[@i] = t} + {v[@i] <> t}).
  intros.
  specialize (X (Fin.FS i) t); auto.
  specialize (IHn _ v v' X0).
  specialize (X Fin.F1 h0); simpl in X.
  destruct IHn; destruct X; subst;
  try (left; auto; fail).
  right; intro; inversion H; auto.
  right; intro; inversion H; auto; apply inj_pair2_eq_dec in H1; auto.
  right; intro; inversion H; auto; apply inj_pair2_eq_dec in H1; auto.
Qed.

Lemma eq_vector_dec : forall {n A} (P : forall (t t' : A), {t = t'} + {t <> t'}) (v v' : Vector.t A n), {v = v'} + {v <> v'}.
Proof.
  intros. apply eq_vector_dec_ind.
  intros. apply P.
Qed.

Hint Immediate eq_vector_dec.

Lemma lift_fin_inj : forall {n} m (i : Fin.t n) j,
                       Fin.R m i = Fin.R m j -> i = j.
Proof.
  induction m; intros; simpl in H; auto.
  inversion H. apply inj_pair2_eq_dec in H1; eauto.
Qed.

Lemma vector_map_map : forall {n A B C} (f : B->C) (g:A->B) (v : Vector.t A n),
                         Vector.map f (Vector.map g v) = Vector.map (fun x => f (g x)) v.
Proof.
  induction v; auto.
  simpl. f_equal. auto.
Qed.

Lemma vector_map_inj : forall {n A B} (f : A -> B) (v v' : Vector.t A n)
                       (P : forall i t', f v[@i] = f t' -> v[@i] = t'),
                         Vector.map f v = Vector.map f v' -> v = v'.
Proof.
  induction v; intros; dependent destruction v'; auto.
  intros. f_equal. 
  inversion H. specialize (P Fin.F1 h0). auto.
  assert (forall (i : Fin.t n) (t' : A), f v[@i] = f t' -> v[@i] = t').
  intros. specialize (P (Fin.FS i) t'). simpl in P. auto.
  specialize (IHv v' H0).
  inversion H. apply inj_pair2_eq_dec in H3; auto.
Qed.

Lemma fin_compare : forall {n}, Fin.t n -> Fin.t n -> comparison.
Proof.
  intros n. induction n.
  intros. apply Fin.case0; eauto.
  intros x y. fin_dep_destruct x; fin_dep_destruct y.
  apply Eq.
  apply Lt.
  apply Gt.
  apply IHn; eauto.
Qed.

Fixpoint fin_subst {A n} (t : A) (x : Fin.t (S n)) (y : Fin.t (S n)) : A + Fin.t n :=
  match n as n' return forall pf : n' = n, A + Fin.t n with
    | O => fun _ => inl t
    | S n' => fun pf =>
                match x in Fin.t m return forall pf : m = S n,
                                            A + Fin.t n with
                  | Fin.F1 _ => fun pfx =>
                                  match y in Fin.t m return forall pf : m = S n,
                                                              A + Fin.t n with
                                    | Fin.F1 _ => fun pfy => inl t
                                    | Fin.FS m y => fun pfy => inr (eq_rect m Fin.t y _ (f_equal pred pfy))
                                  end eq_refl
                  | Fin.FS k x => fun pfx =>
                                  match y in Fin.t m return forall pf : m = S n,
                                                              A + Fin.t n with
                                    | Fin.F1 _ => fun pfy => inr (eq_rect (S n') Fin.t Fin.F1 _ pf)
                                    | Fin.FS m y => fun pfy =>
                                                      match @fin_subst A n' t
                                                                       (eq_rect k Fin.t x _ (eq_trans (f_equal pred pfx) (eq_sym pf)))
                                                                       (eq_rect m Fin.t y _ (eq_trans (f_equal pred pfy) (eq_sym pf))) with
                                                        | inl t => inl t
                                                        | inr v => inr (eq_rect (S n') Fin.t (Fin.FS v) _ pf)
                                                      end
                                  end eq_refl
                end eq_refl
  end eq_refl.

Lemma fin_subst_eq : forall n A (t : A) (x : Fin.t (S n)), fin_subst t x x = inl t.
Proof with eauto.
  induction n; intros; fin_dep_destruct x; simpl...
  rewrite IHn...
Qed.

Lemma fin_subst_neq : forall n A B (t : A) (t' : B) (x y : Fin.t (S n)),
                        x <> y -> exists v, fin_subst t x y = inr v /\
                                            fin_subst t' x y = inr v.
Proof with eauto.
  induction n; dependent destruction x; dependent destruction y; intro;
  try (exfalso; eauto; fail);
  try (eapply Fin.case0; eauto; fail);
  try (eexists; split; simpl; eauto; fail).
  assert (x <> y); [intro; subst; apply H; auto|];
  specialize (IHn _ _ t t' x y H0); destruct IHn; destruct_pairs;
  eexists; simpl; rewrite H1; rewrite H2; split; eauto.
Qed.

Lemma eq_fin_subst : forall n A (t t' : A) (x y : Fin.t (S n)), fin_subst t x y = inl t' -> t = t'.
Proof with eauto.
  dependent induction n; intros;
  dependent destruction x; dependent destruction y;
  try (inversion H; auto).
  destruct (fin_subst t x y) eqn:H2; inversion H; inversion H1; subst...
Qed.

Ltac simpl_exist :=
  repeat (
      repeat match goal with
               | [ H : existT _ _ _ = existT _ _ _ |- _] =>
                 (apply inj_pair2_eq_dec in H; [|eauto using eq_vector_dec; fail])
               | [ H : existT _ _ _ = existT _ _ _, _ : existT _ _ _ = existT _ _ _ |- _] =>
                 (apply inj_pair2_eq_dec in H; [|eauto using eq_vector_dec; fail])
               | [ H : existT _ _ _ = existT _ _ _, _ : existT _ _ _ = existT _ _ _, _ : existT _ _ _ = existT _ _ _ |- _] =>
                 (apply inj_pair2_eq_dec in H; [|eauto using eq_vector_dec; fail])
             end;
      subst; clear_dups
    ).

Ltac simpl_forall_list :=
  repeat match goal with
           | [ H : Forall _ ?l |- _ ] => is_list_constr l; inversion_clear H
           | _ => idtac
         end.

Module Type TermDef.
  Parameter symbol : Type.
  Parameter eq_symbol_dec : forall (s s' : symbol), {s = s'} + {s <> s'}.
  Hint Immediate eq_symbol_dec.
  Parameter arity : symbol -> nat.
End TermDef.

Module Expr (T : TermDef).
  Import T.
  Export T.

  Inductive term : nat -> Type :=
  | t_var : forall {n}, Fin.t n -> term n
  | t_term : forall {n} (s : symbol), Vector.t (term n) (arity s) -> term n
  .
  
  Definition termRect :=
      fun (P : forall n : nat, term n -> Type)
          (f : forall (n : nat) (t : Fin.t n), P n (@t_var n t))
          (f0 : forall (n : nat) (s : symbol) (t : Vector.t (term n) (arity s)),
                  (forall i, P n (Vector.nth t i)) -> P n (t_term s t)) =>
        fix F (n : nat) (t : term n) {struct t} : P n t :=
    match t as t0 in (term n0) return (P n0 t0) with
      | t_var n0 t0 => f n0 t0
      | t_term n0 s t0 => f0 n0 s t0 (fun i => F n0 (Vector.nth t0 i))
    end.

  Theorem eq_term_dec : forall {n} (t t' : term n), {t = t'} + {t <> t'}.
  Proof.
    intro. induction t using termRect; intros;
    destruct t'; try (right; intro; solve by inversion).
    assert (H := eq_fin_dec t t0).
    destruct H; subst.
    left; auto.
    right; intro; inversion H; simpl_exist; auto.
    assert (H := eq_symbol_dec s s0).
    destruct H; subst.
    assert (H := eq_vector_dec_ind t t0 X).
    destruct H; subst.
    left; auto.
    right; intro; inversion H; simpl_exist; auto.
    right; intro; inversion H; simpl_exist; auto.
  Qed.

  Hint Immediate eq_term_dec.

  Fixpoint lift_term {n} (t : term n) : term (S n) :=
    match t with
      | t_var _ j => t_var (Fin.R 1 j)
      | t_term _ s ts => t_term s (Vector.map lift_term ts)
    end.

  Fixpoint lift_term_by {n} i (t : term n) : term (i + n) :=
    match i with
      | 0 => t
      | S i => lift_term (lift_term_by i t)
    end.

  Theorem lift_term_inj : forall {n} (t t' : term n),
                            lift_term t = lift_term t' -> t = t'.
  Proof.
    induction t using termRect; intros t' H0; destruct t';
    simpl in H0; try (solve by inversion); inversion H0; simpl_exist; auto.    
    apply vector_map_inj in H3; subst; auto.
  Qed.

  Hint Immediate lift_term_inj.

  Inductive type : nat -> Type :=
  | ty_term : forall {n : nat}, term n -> type n
  | ty_arrow : forall {n : nat}, type n -> type n -> type n
  | ty_forall : forall {n : nat}, type (S n) -> type n
  | ty_exists : forall {n : nat}, type (S n) -> type n
  | ty_bottom : forall {n : nat}, type n
  | ty_copair : forall {n : nat}, type n -> type n -> type n
  | ty_top : forall {n : nat}, type n
  | ty_pair : forall {n : nat}, type n -> type n -> type n
  .

  Ltac lift_dec_eq :=
    match goal with
      | [ |- { ?a ?b = ?a ?b' } + { ?a ?b <> ?a ?b' } ] =>
        let H := fresh "H" in
        let H0 := fresh "H" in
        assert (H : {b = b'} + {b <> b'});
          [ auto
          | destruct H;
            [ left; subst; auto
            | right; unfold not; intros H0; inversion H0; simpl_exist; auto
            ]
          ]
      | [ |- { ?a ?b ?c = ?a ?b' ?c' } + { ?a ?b ?c <> ?a ?b' ?c' } ] =>
        let H := fresh "H" in
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        assert (H : {b = b'} + {b <> b'});
          [ auto
          | assert (H0 : {c = c'} + {c <> c'});
            [ auto
            | destruct H;
              [ destruct H0;
                [ left; subst; auto
                | right; unfold not; intros H1; inversion H1; simpl_exist; auto
                ]
              | right; unfold not; intros H1; inversion H1; simpl_exist; auto
              ]
            ]
          ]
      | [ |- { ?a ?b ?c ?d = ?a ?b' ?c' ?d' } + { ?a ?b ?c ?d <> ?a ?b' ?c' ?d' } ] =>
        let H := fresh "H" in
        let H0 := fresh "H" in
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        assert (H : {b = b'} + {b <> b'});
          [ auto
          | assert (H0 : {c = c'} + {c <> c'});
            [ auto
            | assert (H1 : {d = d'} + {d <> d'});
              [ auto
              | destruct H;
                [ destruct H0;
                  [ destruct H1;
                    [ left; subst; auto
                    | right; unfold not; intros H2; inversion H2; simpl_exist; auto
                    ]
                  | right; unfold not; intros H2; inversion H2; simpl_exist; auto
                  ]
                | right; unfold not; intros H2; inversion H2; simpl_exist; auto
                ]
              ]
            ]
          ]
    end.

  Theorem eq_type_dec : forall {n} (t t' : type n), {t = t'} + {t <> t'}.
  Proof.
    intro. induction t; destruct t';
           try (right; intro; solve by inversion);
           try (lift_dec_eq).
  Qed.

  Hint Immediate eq_type_dec.
  
  Fixpoint lift_type {n} (t : type n) : type (S n) :=
  match t with
    | ty_term _ t => ty_term (lift_term t)
    | ty_arrow _ a b => ty_arrow (lift_type a) (lift_type b)
    | ty_forall _ a => ty_forall (lift_type a)
    | ty_exists _ a => ty_exists (lift_type a)
    | ty_copair _ a b => ty_copair (lift_type a) (lift_type b)
    | ty_bottom _ => ty_bottom
    | ty_pair _ a b => ty_pair (lift_type a) (lift_type b)
    | ty_top _ => ty_top
  end.

  Fixpoint lift_type_by {n} i (t : type n) : type (i + n) :=
    match i with
      | 0 => t
      | S i => lift_type (lift_type_by i t)
    end.

  Theorem lift_type_inj : forall {n} (t t' : type n),
                            lift_type t = lift_type t' -> t = t'.
  Proof.
    induction t; intros t' H; dependent destruction t'; inversion H; simpl_exist; f_equal; auto.
  Qed.

  Hint Immediate lift_type_inj.
  
  Fixpoint term_subst {n} (i : Fin.t (S n)) (t : term n) (u : term (S n)) : term n :=
    match u as u' in term n' return forall pf : n' = S n,
                                      term n
    with
      | t_var n' j => fun pf =>
                       match fin_subst t i (eq_rect n' Fin.t j _ pf) with
                         | inl t => t
                         | inr v => t_var v
                       end
      | t_term n' s ts => fun pf => t_term s (Vector.map (term_subst i t)
                                                         (eq_rect n' (fun i => Vector.t (term i) _) ts _ pf)
                                             )
    end eq_refl.

  Fixpoint type_subst {n} (i : Fin.t (S n)) (t : term n) (u : type (S n)) : type n :=
    match u as u' in type n' return forall pf : n' = S n,
                                      type n
    with
      | ty_term n' a => fun pf => ty_term (term_subst i t (eq_rect n' term a _ pf))
      | ty_arrow n' a b => fun pf => ty_arrow (type_subst i t (eq_rect n' type a _ pf)) (type_subst i t (eq_rect n' type b _ pf))
      | ty_forall n' a => fun pf => ty_forall (type_subst (Fin.R 1 i) (lift_term t) (eq_rect (S n') type a _ (f_equal S pf)))
      | ty_exists n' a => fun pf => ty_exists (type_subst (Fin.R 1 i) (lift_term t) (eq_rect (S n') type a _ (f_equal S pf)))
      | ty_copair n' a b => fun pf => ty_copair (type_subst i t (eq_rect n' type a _ pf)) (type_subst i t (eq_rect n' type b _ pf))
      | ty_bottom _ => fun pf => ty_bottom
      | ty_pair n' a b => fun pf => ty_pair (type_subst i t (eq_rect n' type a _ pf)) (type_subst i t (eq_rect n' type b _ pf))
      | ty_top _ => fun pf => ty_top
    end eq_refl.

    Inductive exp : nat -> nat -> Type :=
    | e_var : forall {n m : nat}, Fin.t n -> exp n m
    | e_app : forall {n m : nat}, exp n m -> exp n m -> exp n m
    | e_forall : forall {n m : nat}, exp n (S m) -> exp n m
    | e_exists : forall {n m : nat}, term m -> exp n m -> exp n m
    | e_ecase : forall {n m : nat}, exp n m -> exp (S n) (S m) -> exp n m
    | e_abs : forall {n m : nat}, exp (S n) m -> exp n m
    | e_tapp : forall {n m : nat}, exp n m -> term m -> exp n m
    | e_absurd : forall {n m}, exp n m -> exp n m
    | e_copair1 : forall {n m}, exp n m -> exp n m
    | e_copair2 : forall {n m}, exp n m -> exp n m
    | e_case : forall {n m}, exp n m -> exp (S n) m -> exp (S n) m -> exp n m
    | e_tt : forall {n m}, exp n m
    | e_pair : forall {n m}, exp n m -> exp n m -> exp n m
    | e_pair1 : forall {n m}, exp n m -> exp n m
    | e_pair2 : forall {n m}, exp n m -> exp n m
    .

    Theorem eq_exp_dec : forall {n m} (e e' : exp n m), {e = e'} + {e <> e'}.
    Proof.
      intros n m. induction e; destruct e';
                  try (right; intro; solve by inversion);
                  try (lift_dec_eq).
    Qed.
    
    Hint Immediate eq_exp_dec.
  

  Definition sub_exp {n m} (t : exp n m) : list (exp n m) :=
  match t with
    | e_var _ _ j => nil
    | e_app _ _ a b => cons a (cons b nil)
    | e_forall _ _ a => nil
    | e_exists _ _ a b => nil
    | e_ecase _ _ a b => nil
    | e_abs _ _ a => nil
    | e_tapp _ _ a b => nil
    | e_absurd _ _ a => cons a nil
    | e_copair1 _ _ a => cons a nil
    | e_copair2 _ _ a => cons a nil
    | e_case _ _ a b c => cons a nil
    | e_tt _ _ => nil
    | e_pair _ _ a b => cons a (cons b nil)
    | e_pair1 _ _ a => cons a nil
    | e_pair2 _ _ a => cons a nil
  end.

  Fixpoint lift_exp_n {n m} (t : exp n m) : exp (S n) m :=
  match t with
    | e_var _ _ j => e_var (Fin.FS j)
    | e_app _ _ a b => e_app (lift_exp_n a) (lift_exp_n b)
    | e_forall _ _ a => e_forall (lift_exp_n a)
    | e_exists _ _ a b => e_exists a (lift_exp_n b)
    | e_ecase _ _ a b => e_ecase (lift_exp_n a) (lift_exp_n b)
    | e_abs _ _ a => e_abs (lift_exp_n a)
    | e_tapp _ _ a b => e_tapp (lift_exp_n a) b
    | e_absurd _ _ a => e_absurd (lift_exp_n a)
    | e_copair1 _ _ a => e_copair1 (lift_exp_n a)
    | e_copair2 _ _ a => e_copair2 (lift_exp_n a)
    | e_case _ _ a b c => e_case (lift_exp_n a) (lift_exp_n b) (lift_exp_n c)
    | e_tt _ _ => e_tt
    | e_pair _ _ a b => e_pair (lift_exp_n a) (lift_exp_n b)
    | e_pair1 _ _ a => e_pair1 (lift_exp_n a)
    | e_pair2 _ _ a => e_pair2 (lift_exp_n a)
  end.
  
  Fixpoint lift_exp {n m} (t : exp n m) : exp n (S m) :=
  match t with
    | e_var _ _ j => e_var j
    | e_app _ _ a b => e_app (lift_exp a) (lift_exp b)
    | e_forall _ _ a => e_forall (lift_exp a)
    | e_exists _ _ a b => e_exists (lift_term a) (lift_exp b)
    | e_ecase _ _ a b => e_ecase (lift_exp a) (lift_exp b)
    | e_abs _ _ a => e_abs (lift_exp a)
    | e_tapp _ _ a b => e_tapp (lift_exp a) (lift_term b)
    | e_absurd _ _ a => e_absurd (lift_exp a)
    | e_copair1 _ _ a => e_copair1 (lift_exp a)
    | e_copair2 _ _ a => e_copair2 (lift_exp a)
    | e_case _ _ a b c => e_case (lift_exp a) (lift_exp b) (lift_exp c)
    | e_tt _ _ => e_tt
    | e_pair _ _ a b => e_pair (lift_exp a) (lift_exp b)
    | e_pair1 _ _ a => e_pair1 (lift_exp a)
    | e_pair2 _ _ a => e_pair2 (lift_exp a)
  end.

    Fixpoint exp_subst {n m} (i : Fin.t (S n)) (t : exp n m) (u : exp (S n) m) : exp n m :=
      let eq_rect_exp {n m n' m'} (pf : n' = S n) (pf' : m' = m) x :=
          eq_rect n' (fun i => exp i m) (eq_rect m' (fun i => exp n' i) x _ pf') _ pf
      in
      match u as u' in exp n' m' return forall pf : n' = S n,
                                        forall pf' : m' = m,
                                          exp n m
      with
        | e_var n' _ j => fun pf _ =>
                            match fin_subst t i (eq_rect n' Fin.t j _ pf) with
                              | inl t => t
                              | inr v => e_var v
                            end
        | e_app _ _ a b => fun pf pf' => e_app (exp_subst i t (eq_rect_exp pf pf' a)) (exp_subst i t (eq_rect_exp pf pf' b))
        | e_forall _ _ a => fun pf pf' => e_forall (exp_subst i (lift_exp t) (eq_rect_exp pf (f_equal S pf') a))
        | e_exists _ m' a b => fun pf pf' => e_exists (eq_rect m' term a _ pf') (exp_subst i t (eq_rect_exp pf pf' b))
        | e_ecase _ _ a b => fun pf pf' => e_ecase (exp_subst i t (eq_rect_exp pf pf' a)) (exp_subst (Fin.FS i) (lift_exp_n (lift_exp t)) (eq_rect_exp (f_equal S pf) (f_equal S pf') b))
        | e_abs _ _ a => fun pf pf' => e_abs (exp_subst (Fin.FS i) (lift_exp_n t) (eq_rect_exp (f_equal S pf) pf' a))
        | e_tapp _ _ a b => fun pf pf' => e_tapp (exp_subst i t (eq_rect_exp pf pf' a)) (eq_rect _ _ b _ pf')
        | e_absurd _ _ a => fun pf pf' => e_absurd (exp_subst i t (eq_rect_exp pf pf' a))
        | e_copair1 _ _ a => fun pf pf' => e_copair1 (exp_subst i t (eq_rect_exp pf pf' a))
        | e_copair2 _ _ a => fun pf pf' => e_copair2 (exp_subst i t (eq_rect_exp pf pf' a))
        | e_case _ _ a b c => fun pf pf' => e_case
                                              (exp_subst i t (eq_rect_exp pf pf' a))
                                              (exp_subst (Fin.FS i) (lift_exp_n t) (eq_rect_exp (f_equal S pf) pf' b))
                                              (exp_subst (Fin.FS i) (lift_exp_n t) (eq_rect_exp (f_equal S pf) pf' c))
        | e_tt _ _ => fun _ _ => e_tt
        | e_pair _ _ a b => fun pf pf' => e_pair (exp_subst i t (eq_rect_exp pf pf' a)) (exp_subst i t (eq_rect_exp pf pf' b))
        | e_pair1 _ _ a => fun pf pf' => e_pair1 (exp_subst i t (eq_rect_exp pf pf' a))
        | e_pair2 _ _ a => fun pf pf' => e_pair2 (exp_subst i t (eq_rect_exp pf pf' a))
      end eq_refl eq_refl.
    Reserved Notation "a '===>' b" (at level 60).

    Fixpoint exp_subst_term {n m} (i : Fin.t (S m)) (t : term m) (u : exp n (S m)) : exp n m :=
      let eq_rect_exp {n m n' m'} (pf : n' = n) (pf' : m' = S m) (x : exp n' m') :=
          eq_rect n' (fun i => exp i (S m)) (eq_rect m' (fun i => exp n' i) x _ pf') _ pf
      in
      match u as u' in exp n' m' return forall pf : n' = n,
                                        forall pf' : m' = S m,
                                          exp n m
      with
        | e_var n' _ j => fun pf pf' => eq_rect n' (fun i => exp i m) (e_var j) _ pf
        | e_app _ _ a b => fun pf pf' => e_app (exp_subst_term i t (eq_rect_exp pf pf' a)) (exp_subst_term i t (eq_rect_exp pf pf' b))
        | e_forall _ _ a => fun pf pf' => e_forall (exp_subst_term (Fin.FS i) (lift_term t) (eq_rect_exp pf (f_equal S pf') a))
        | e_exists _ m' a b => fun pf pf' => e_exists (term_subst i t (eq_rect m' term a _ pf')) (exp_subst_term i t (eq_rect_exp pf pf' b))
        | e_ecase _ _ a b => fun pf pf' => e_ecase (exp_subst_term i t (eq_rect_exp pf pf' a)) (exp_subst_term (Fin.FS i) (lift_term t) (eq_rect_exp (f_equal S pf) (f_equal S pf') b))
        | e_abs _ _ a => fun pf pf' => e_abs (exp_subst_term i t (eq_rect_exp (f_equal S pf) pf' a))
        | e_tapp _ m' a b => fun pf pf' => e_tapp (exp_subst_term i t (eq_rect_exp pf pf' a)) (term_subst i t (eq_rect m' term b _ pf'))
        | e_absurd _ _ a => fun pf pf' => e_absurd (exp_subst_term i t (eq_rect_exp pf pf' a))
        | e_copair1 _ _ a => fun pf pf' => e_copair1 (exp_subst_term i t (eq_rect_exp pf pf' a))
        | e_copair2 _ _ a => fun pf pf' => e_copair2 (exp_subst_term i t (eq_rect_exp pf pf' a))
        | e_case _ _ a b c => fun pf pf' => e_case
                                              (exp_subst_term i t (eq_rect_exp pf pf' a))
                                              (exp_subst_term i t (eq_rect_exp (f_equal S pf) pf' b))
                                              (exp_subst_term i t (eq_rect_exp (f_equal S pf) pf' c))
        | e_tt _ _ => fun _ _ => e_tt
        | e_pair _ _ a b => fun pf pf' => e_pair (exp_subst_term i t (eq_rect_exp pf pf' a)) (exp_subst_term i t (eq_rect_exp pf pf' b))
        | e_pair1 _ _ a => fun pf pf' => e_pair1 (exp_subst_term i t (eq_rect_exp pf pf' a))
        | e_pair2 _ _ a => fun pf pf' => e_pair2 (exp_subst_term i t (eq_rect_exp pf pf' a))
      end eq_refl eq_refl.
    
    Reserved Notation "a '===>' b" (at level 60).

    Inductive reduction : forall {n m}, exp n m -> exp n m -> Prop :=
    | reduction_beta : forall n m (a : exp (S n) m) b, e_app (e_abs a) b ===> exp_subst Fin.F1 b a
    | reduction_forall : forall n m (a : exp n (S m)) (b : term m), reduction (e_tapp (e_forall a) b) (exp_subst_term Fin.F1 b a)
    | reduction_absurd : forall n m (a : exp n m) b, e_app (e_absurd a) b ===> e_absurd a
    | reduction_ecase : forall n m t (a : exp n m) b, e_ecase (e_exists t a) b ===> exp_subst Fin.F1 a (exp_subst_term Fin.F1 t b)
    | reduction_case1 : forall n m (a : exp n m) u v, e_case (e_copair1 a) u v ===> exp_subst Fin.F1 a u
    | reduction_case2 : forall n m (a : exp n m) u v, e_case (e_copair2 a) u v ===> exp_subst Fin.F1 a v
    | reduction_pair1 : forall n m (a : exp n m) b, e_pair1 (e_pair a b) ===> a
    | reduction_pair2 : forall n m (a : exp n m) b, e_pair2 (e_pair a b) ===> b
    | reduction_context_app_1 : forall n m (a : exp n m) b a', a ===> a' -> e_app a b ===> e_app a' b
    | reduction_context_app_2 : forall n m (b : exp n m) a b', b ===> b' -> e_app a b ===> e_app a b'
    | reduction_context_abs : forall n m (a : exp (S n) m) a', a ===> a' -> e_abs a ===> e_abs a'
    | reduction_context_forall : forall n m (a : exp n (S m)) a', a ===> a' -> e_forall a ===> e_forall a'
    | reduction_context_exists : forall n m (a : exp n m) a' t, a ===> a' -> e_exists t a ===> e_exists t a'
    | reduction_context_ecase_1 : forall n m (a : exp n m) b a', a ===> a' -> e_ecase a b ===> e_ecase a' b
    | reduction_context_ecase_2 : forall n m (a : exp n m) b b', b ===> b' -> e_ecase a b ===> e_ecase a b'
    | reduction_context_tapp : forall n m (a : exp n m) a' t, a ===> a' -> e_tapp a t ===> e_tapp a' t
    | reduction_context_absurd : forall n m (a : exp n m) a', a ===> a' -> e_absurd a ===> e_absurd a'
    | reduction_context_case_1 : forall n m (a : exp n m) b c a', a ===> a' -> e_case a b c ===> e_case a' b c
    | reduction_context_case_2 : forall n m (a : exp n m) b c b', b ===> b' -> e_case a b c ===> e_case a b' c
    | reduction_context_case_3 : forall n m (a : exp n m) b c c', c ===> c' -> e_case a b c ===> e_case a b c'
    | reduction_context_copair1 : forall n m (a : exp n m) a', a ===> a' -> e_copair1 a ===> e_copair1 a'
    | reduction_context_copair2 : forall n m (a : exp n m) a', a ===> a' -> e_copair2 a ===> e_copair2 a'
    | reduction_context_pair_1 : forall n m (a : exp n m) b a', a ===> a' -> e_pair a b ===> e_pair a' b
    | reduction_context_pair_2 : forall n m (a : exp n m) b b', b ===> b' -> e_pair a b ===> e_pair a b'
    | reduction_context_pair1 : forall n m (a : exp n m) a', a ===> a' -> e_pair1 a ===> e_pair1 a'
    | reduction_context_pair2 : forall n m (a : exp n m) a', a ===> a' -> e_pair2 a ===> e_pair2 a'
    (* | reduction_trans : forall n m (a : exp n m) b c, a ===> b -> b ===> c -> a ===> c *)
    where "a '===>' b" := (@reduction _ _ a b)
    .

    Definition nf {n m} (e : exp n m) := forall e', e ===> e' -> False.

    Theorem nf_sub_exp : forall {n m} (e : exp n m), nf e -> Forall nf (sub_exp e).
    Proof.
      unfold nf; intros.
      destruct e; simpl; repeat constructor; intros e' He;
      eapply H; try (constructor; eauto; fail).
      eapply reduction_context_app_2; eauto.
      eapply reduction_context_pair_2; eauto.
    Qed.
    
    Inductive nfview : forall {n m}, exp n m -> Prop :=
    | nfv_unknown : forall n m (e : exp n m) (ns : list (exp n m)),
                      Forall nfview ns -> nfview_unknown e ->
                      nfview (fold_right (fun a b => e_app b a) e ns)
    | nfv_abs : forall n m (e : exp (S n) m),
                  nfview e -> nfview (e_abs e)
    | nfv_absurd : forall n m (e : exp n m),
                  nfview e -> nfview (e_absurd e)
    with nfview_unknown : forall {n m}, exp n m -> Prop :=
         | nfv_var : forall n m (i : Fin.t n), @nfview_unknown _ m (e_var i)
         | nfv_forall : forall n m (e : exp n (S m)),
                          nfview e -> nfview_unknown (e_forall e)
         | nfv_exists : forall n m t (e : exp n m),
                          nfview e -> nfview_unknown (e_exists t e)
         | nfv_ecase : forall n m (a : exp n m) (b : exp (S n) (S m)),
                         (forall x y, a = e_exists x y -> False) ->
                         nfview a -> nfview b -> nfview_unknown (e_ecase a b)
         | nfv_tapp : forall n m (a : exp n m) t,
                        (forall x, a = e_forall x -> False) ->
                        nfview a -> nfview_unknown (e_tapp a t)
         | nfv_copair1 : forall n m (a : exp n m),
                           nfview a -> nfview_unknown (e_copair1 a)
         | nfv_copair2 : forall n m (a : exp n m),
                           nfview a -> nfview_unknown (e_copair2 a)
         | nfv_case : forall n m (a : exp n m) b c,
                        (forall x, a = e_copair1 x -> False) ->
                        (forall x, a = e_copair2 x -> False) ->
                        nfview a -> nfview b -> nfview c -> nfview_unknown (e_case a b c)
         | nfv_tt : forall n m, @nfview_unknown n m e_tt
         | nfv_pair : forall n m (a : exp n m) b,
                        nfview a -> nfview b -> nfview_unknown (e_pair a b)
         | nfv_pair1 : forall n m (a : exp n m),
                         (forall x y, a = e_pair x y -> False) ->
                         nfview a -> nfview_unknown (e_pair1 a)
         | nfv_pair2 : forall n m (a : exp n m),
                         (forall x y, a = e_pair x y -> False) ->
                         nfview a -> nfview_unknown (e_pair2 a)
    .
    
    Ltac nf_nfview_helper p := 
      match goal with
        | [ IH : nf ?e -> nfview ?e |- nfview ?e ] =>
          let e := fresh "e" in
          let H := fresh "H" in
          apply IH; intros e H; exfalso; eapply p; constructor (solve [eauto])
      end.

    Theorem nf_nfview : forall n m (e : exp n m), nf e -> nfview e.
    Proof with eauto; try (constructor; eauto; fail).
      intros n m e. set (e0 := e).
      dependent induction e; intro p;
      assert (A := nf_sub_exp e0 p); subst e0; simpl in A; simpl_forall_list;
      repeat match goal with
                 [ A : nf ?e -> nfview ?e, B : nf ?e |- _ ] => apply A in B
             end;
      try (apply nfv_unknown with (ns:=nil); eauto; constructor; eauto;
           try (nf_nfview_helper p; fail);
           try (intros; subst; eapply p; constructor);
           fail);
      try (constructor (solve [eauto; nf_nfview_helper p]); fail).
      + destruct H; try (exfalso; eapply p; constructor; fail).
        apply nfv_unknown with (e:=e) (ns:=cons e2 ns)...
    Qed.

    Theorem nfview_nf : forall n m (e : exp n m), (nfview e -> nf e) /\ (nfview_unknown e -> nf e).
    Proof with eauto.
      intros n m e; set (e0 := e); dependent induction e;
      (assert (S2 : nfview_unknown e0 -> nf e0);
      [ subst e0; intro;
        destruct_pairs;
        try (intros e' H'; inversion H'; fail);
        inversion H; simpl_exist; subst; eauto
      | split; [|exact S2]; subst e0; intro;
        destruct_pairs;
        inversion H; simpl_exist; subst;
        try (match goal with
                 [ H : fold_right _ _ _ = _ |- _ ] => destruct ns; [ simpl in H; subst; auto
                                                                   | solve by inversion
                                                                   ]
             end; fail)
      ]); try (intros e' H'; inversion H'; simpl_exist; subst; eauto;
               match goal with 
                 | [ H : nfview ?e -> nf ?e, _ : ?e ===> _ |- _ ] => unfold nf in H; eapply H; eauto
               end; fail
              ).
      + destruct ns; simpl in H4; subst; [ solve by inversion |].
        destruct ns; simpl in H4; inversion H4; simpl_exist; subst.
        * simpl_forall_list.
          intros e' H'; inversion H'; simpl_exist; subst.
          inversion H8.
          inversion H8.
          unfold nf in H3; eapply H3; eauto.
          unfold nf in H0; eapply H0; eauto.
        * simpl_forall_list.
          intros e' H'; inversion H'; simpl_exist; subst.
          unfold nf in H2; eapply H2... apply nfv_unknown with (e:=e) (ns:=cons e3 ns)...
          unfold nf in H0; eapply H0; eauto.
    Qed.

    Theorem nfview_app : forall {n m} (a b : exp n m), nfview (e_app a b) -> nfview a.
    Proof.
      intros.
      apply nfview_nf in H.
      apply nf_nfview. intro. intros. eapply H. eapply reduction_context_app_1. eauto.
    Qed.
      
End Expr.

Module Type TermCongruence (T : TermDef).
  Module E := Expr(T).
  Import E.
  Export E.
  Parameter cong : forall {n}, type n -> type n -> Prop.
End TermCongruence.

Module NJ (T : TermDef) (TC : TermCongruence(T)).
  Import TC.
  Export TC.
  Reserved Notation "x '≡' y" (at level 40).

  Inductive type_equiv : forall {n : nat}, relation (type n) :=
  | te_context_var : forall {n} {i}, @ty_term n (t_var i) ≡ ty_term (t_var i)
  | te_context_term : forall {n} {s : symbol} xs ys,
                        (forall i, @ty_term n (Vector.nth xs i) ≡ ty_term (Vector.nth ys i)) ->
                        ty_term (t_term s xs) ≡ ty_term (t_term s ys)
  | te_context_arrow : forall {n} {x y z t : type n},
                         x ≡ y ->
                         z ≡ t ->
                         ty_arrow x z ≡ ty_arrow y t
  | te_context_forall : forall {n} {x y : type (S n)},
                          x ≡ y ->
                          ty_forall x ≡ ty_forall y
  | te_context_exists : forall {n} {x y : type (S n)},
                          x ≡ y ->
                          ty_exists x ≡ ty_exists y
  | te_context_bottom : forall {n}, @ty_bottom n ≡ ty_bottom
  | te_context_copair : forall {n} {x y z t : type n},
                         x ≡ y ->
                         z ≡ t ->
                         ty_copair x z ≡ ty_copair y t
  | te_context_top : forall {n}, @ty_top n ≡ ty_top
  | te_context_pair : forall {n} {x y z t : type n},
                         x ≡ y ->
                         z ≡ t ->
                         ty_pair x z ≡ ty_pair y t
  | te_sym : forall {n} {x y : type n}, x ≡ y -> y ≡ x
  | te_trans : forall {n} {x y z : type n}, x ≡ y -> y ≡ z -> x ≡ z
  | te_term : forall {n} {x y : type n},
                cong x y -> x ≡ y
  | te_subst : forall {n i t} {x y : type (S n)},
                      x ≡ y -> type_subst i t x ≡ type_subst i t y
  where "x '≡' y" := (type_equiv x y).
  
  Theorem te_refl : forall {n : nat} (x : type n), x ≡ x.
  Proof.
    assert (forall n (t : term n), ty_term t ≡ ty_term t).
    induction t using termRect; constructor; eauto.
    induction x; try (constructor; eauto; fail).
  Qed.
  
  Definition liftΓ {n m} (Γ : Vector.t (type m) n) : Vector.t (type (S m)) n := Vector.map lift_type Γ.

  Theorem liftΓ_inj : forall {n m} (Γ1 Γ2 : Vector.t (type m) n),
                        liftΓ Γ1 = liftΓ Γ2 -> Γ1 = Γ2.
  Proof.
    induction Γ1; intros; dependent destruction Γ2; auto.
    simpl in H. inversion H. f_equal; simpl_exist; auto.
  Qed.

  Hint Immediate liftΓ_inj.
  
  Reserved Notation "Γ '⊢' t '∈' ty" (at level 40).
  
  Inductive has_type : forall {n m : nat}, Vector.t (type m) n -> exp n m -> type m -> Prop :=
  | p_var : forall {n m} {Γ : Vector.t (type m) n} i ty,
              ty ≡ Vector.nth Γ i -> Γ ⊢ e_var i ∈ ty
  | p_app : forall {n m} {Γ : Vector.t (type m) n} {u v s t ty},
            Γ ⊢ u ∈ ty_arrow s t ->
            Γ ⊢ v ∈ s ->
            ty ≡ t -> Γ ⊢ e_app u v ∈ ty
  | p_abs : forall {n m} {Γ : Vector.t (type m) n} {e t u ty},
              (t :: Γ) ⊢ e ∈ u ->
              ty ≡ ty_arrow t u -> Γ ⊢ e_abs e ∈ ty
  | p_forall : forall {n m} {Γ : Vector.t (type m) n} {e u ty},
                 (liftΓ Γ) ⊢ e ∈ u ->
                 ty ≡ ty_forall u -> Γ ⊢ e_forall e ∈ ty
  | p_exists : forall {n m} {Γ : Vector.t (type m) n} {t u p ty},
                 Γ ⊢ u ∈ type_subst Fin.F1 t p ->
                 ty ≡ ty_exists p -> Γ ⊢ e_exists t u ∈ ty
  | p_ecase : forall {n m} {Γ : Vector.t (type m) n} {u v p q ty},
                Γ ⊢ u ∈ ty_exists p ->
                (p :: liftΓ Γ) ⊢ v ∈ lift_type q ->
                ty ≡ q -> Γ ⊢ e_ecase u v ∈ ty
  | p_copair1 : forall {n m} {Γ : Vector.t (type m) n} {u s t ty},
                  Γ ⊢ u ∈ s ->
                  ty ≡ ty_copair s t -> Γ ⊢ e_copair1 u ∈ ty
  | p_copair2 : forall {n m} {Γ : Vector.t (type m) n} {v s t ty},
                  Γ ⊢ v ∈ t ->
                  ty ≡ ty_copair s t -> Γ ⊢ e_copair2 v ∈ ty
  | p_case : forall {n m} {Γ : Vector.t (type m) n} {a b u v1 v2 t ty},
               Γ ⊢ u ∈ ty_copair a b ->
               (a :: Γ) ⊢ v1 ∈ t ->
               (b :: Γ) ⊢ v2 ∈ t ->
               ty ≡ t -> Γ ⊢ e_case u v1 v2 ∈ ty
  | p_pair : forall {n m} {Γ : Vector.t (type m) n} {u v s t ty},
               Γ ⊢ u ∈ s ->
               Γ ⊢ v ∈ t ->
               ty ≡ ty_pair s t -> Γ ⊢ e_pair u v ∈ ty
  | p_pair1 : forall {n m} {Γ : Vector.t (type m) n} {u s t ty},
                  Γ ⊢ u ∈ ty_pair s t ->
                  ty ≡ s -> Γ ⊢ e_pair1 u ∈ ty
  | p_pair2 : forall {n m} {Γ : Vector.t (type m) n} {u s t ty},
                  Γ ⊢ u ∈ ty_pair s t ->
                  ty ≡ t -> Γ ⊢ e_pair2 u ∈ ty
  | p_absurd : forall {n m} {Γ : Vector.t (type m) n} {e t ty},
                 Γ ⊢ e ∈ ty_bottom ->
                 ty ≡ t -> Γ ⊢ e_absurd e ∈ ty
  | p_tt : forall {n m} {Γ : Vector.t (type m) n} {ty},
             ty ≡ ty_top -> Γ ⊢ e_tt ∈ ty
               where "Γ '⊢' t '∈' ty" := (has_type Γ t ty).
    
  Definition is_typable {n m : nat} (e : exp n m) := sigma Γ ty, Γ ⊢ e ∈ ty.
  Definition is_provable {n : nat} (ty : type n) := sigma {e : exp O n}, [] ⊢ e ∈ ty.
  Definition is_provable_nf {n : nat} (ty : type n) := (sigma {e : exp O n}, nf e * ([] ⊢ e ∈ ty))%type.
  
End NJ.

Module Ex1Term <: TermDef.
  Inductive symbol_ :=
  | s_zero
  | s_succ
  | s_plus
  | s_equal
  .

  Definition symbol := symbol_.

  Theorem eq_symbol_dec : forall (s s' : symbol), {s = s'} + {s <> s'}.
  Proof.
    decide equality.
  Qed.
    
  Fixpoint arity s :=
    match s with
      | s_zero => 0
      | s_succ => 1
      | s_plus => 2
      | s_equal => 2
    end.
End Ex1Term.

Module Ex1Congruence <: TermCongruence(Ex1Term).
  Module E := Expr(Ex1Term).
  Import E.
  Export E.
  
  Inductive cong_ {n} : relation (type n) :=
  | c_0_l : forall {x}, cong_ (ty_term (t_term s_plus [t_term s_zero []; x])) (ty_term x)
  | c_S_l : forall {x y}, cong_ (ty_term (t_term s_plus [t_term s_succ [x]; y])) (ty_term (t_term s_succ [t_term s_plus [x;  y]]))
  | c_plus_sym : forall {x y}, cong_ (ty_term (t_term s_plus [x; y])) (ty_term (t_term s_plus [y; x]))
  | c_equal_sym : forall {x y}, cong_ (ty_term (t_term s_equal [x; y])) (ty_term (t_term s_equal [y; x]))
  | c_refl : forall {x}, cong_ (ty_term (t_term s_equal [x; x])) ty_top
  | c_neq_0 : forall {x}, cong_ (ty_term (t_term s_equal [t_term s_succ [x]; t_term s_zero []])) ty_bottom
  | c_S_inj : forall {x y}, cong_ (ty_term (t_term s_equal [t_term s_succ [x]; t_term s_succ [y]]))
                                  (ty_term (t_term s_equal [x; y]))
  .
  Definition cong {n} := @cong_ n.
End Ex1Congruence.

Module Ex1NJ := NJ(Ex1Term)(Ex1Congruence).

Module Q1.
  Import Ex1NJ.

  Fixpoint t_of_nat {m} n : term m :=
    match n with
      | 0 => t_term s_zero []
      | S n => t_term s_succ [t_of_nat n]
    end.

  (* TODO : generate tactic by reflection from cong ? *)
  (* TODO : generalize eapply te_context_term ? *)
  Ltac simpl_equiv :=
  autounfold;
  let rec simpl_equiv' :=
  match goal with
    | [ |- ?x ≡ ?x ] => eapply te_refl
    | [ |- ty_term (t_term s_succ [?x]) ≡ _ ] =>
        let ty := type of x in
        let x' := fresh "x" in
        evar (x':ty); apply te_context_term with (ys:=[x']);
        [subst x'; simpl; finite; simpl; simpl_equiv]
    | [ |- ty_term (t_term s_plus [t_term s_zero []; _]) ≡ _ ] =>
      eapply te_trans; [eapply te_term; [eapply c_0_l] | simpl_equiv ]
    | [ |- ty_term (t_term s_plus [t_term s_succ [_]; _]) ≡ _ ] =>
      eapply te_trans; [eapply te_term; [eapply c_S_l] | simpl_equiv ]
    | [ |- ty_term (t_term s_equal [?x; ?y]) ≡ _ ] => eapply te_trans;[
          let ty := type of x in
          let x' := fresh "x" in
          let y' := fresh "y" in
          evar (x':ty); evar (y':ty); apply te_context_term with (ys:=[x'; y']);
          [subst x'; subst y'; simpl; finite; [simpl; simpl_equiv | simpl; simpl_equiv]]
        | match goal with
            | [ |- ty_term (t_term s_equal [t_term s_succ _; t_term s_succ _]) ≡ _ ] =>
              eapply te_trans; [ eapply te_term; [eapply c_S_inj] | simpl_equiv ]
            | [ |- ty_term (t_term s_equal [?x; ?x]) ≡ _ ] =>
              eapply te_trans; [ eapply te_term; [eapply c_refl] | simpl_equiv ]
            | [ |- ty_term (t_term s_equal [t_term s_succ [_]; t_term s_zero []]) ≡ _ ] =>
              eapply te_trans; [ eapply te_term; [eapply c_neq_0] | simpl_equiv ]
            | _ => idtac
          end
        ]
    | [ |- ty_arrow _ _ ≡ ty_arrow _ _ ] => eapply te_context_arrow; [ simpl_equiv | simpl_equiv ]
    | [ |- ty_forall _ ≡ ty_forall _ ] => eapply te_context_forall; [ simpl_equiv ]
    | _ => eapply te_refl
    | _ => idtac
  end in simpl_equiv' || (eapply te_sym; simpl_equiv').
  
  Theorem Q1a : is_provable (@ty_term 0 (t_term s_equal [t_term s_plus [t_of_nat 2; t_of_nat 3]; t_of_nat 5])).
  Proof with eauto.
    eexists e_tt.
    constructor.
    simpl_equiv.
  Qed.
  
  Theorem Q1b : is_provable (@ty_forall 0 (ty_term (t_term s_equal [t_term s_plus [t_of_nat 2; t_var Fin.F1]; t_term s_plus [t_of_nat 1; t_term s_plus [t_of_nat 1; t_var Fin.F1]]]))).
  Proof with eauto.
    eexists (e_forall e_tt).
    repeat (simpl_equiv || econstructor).
  Qed.
  
  Theorem Q1c : is_provable (@ty_arrow 0 (ty_term (t_term s_equal [t_term s_plus [t_of_nat 1; t_of_nat 1]; t_term s_zero []])) (ty_term (t_term s_equal [t_term s_plus [t_of_nat 16; t_of_nat 64]; t_of_nat 42]))).
  Proof with eauto.
    eexists.
    eapply p_abs; [eapply p_absurd;[apply p_var with (i:=Fin.F1)|]|].
    simpl_equiv. simpl_equiv.
    eapply te_context_arrow. simpl_equiv. eapply te_refl.
  Qed.
  
  Theorem Q1d : is_provable (@ty_forall 0 (ty_arrow (ty_term (t_term s_equal [t_var Fin.F1; t_of_nat 2])) (ty_term (t_term s_equal [t_term s_plus [t_of_nat 1; t_var Fin.F1]; t_of_nat 3])))).
  Proof with eauto.
    eexists.
    eapply p_forall;[eapply p_abs;[apply p_var with (i:=Fin.F1)|]|];
    repeat simpl_equiv.
  Qed.

End Q1.

Module Ex2Term <: TermDef.
  Inductive symbol_ :=
  | s_zero
  | s_succ
  | s_plus
  | s_equal
  | s_n
  .
  Definition symbol := symbol_.
  Theorem eq_symbol_dec : forall (s s' : symbol), {s=s'}+{s<>s'}.
  Proof. decide equality. Qed.
  Fixpoint arity s :=
    match s with
      | s_zero => 0
      | s_succ => 1
      | s_plus => 2
      | s_equal => 2
      | s_n => 1
    end.
End Ex2Term.

Module Ex2Congruence <: TermCongruence(Ex2Term).
  Module E := Expr(Ex2Term).
  Import E.
  Export E.
  
  Inductive cong_ {n} : relation (type n) :=
  | c_0_l : forall {x}, cong_ (ty_term (t_term s_plus [t_term s_zero []; x])) (ty_term x)
  | c_S_l : forall {x y}, cong_ (ty_term (t_term s_plus [t_term s_succ [x]; y])) (ty_term (t_term s_succ [t_term s_plus [x;  y]]))
  | c_plus_sym : forall {x y}, cong_ (ty_term (t_term s_plus [x; y])) (ty_term (t_term s_plus [y; x]))
  | c_equal_sym : forall {x y}, cong_ (ty_term (t_term s_equal [x; y])) (ty_term (t_term s_equal [y; x]))
  | c_refl : forall {x}, cong_ (ty_term (t_term s_equal [x; x])) ty_top
  | c_neq_0 : forall {x}, cong_ (ty_term (t_term s_equal [t_term s_succ [x]; t_term s_zero []])) ty_bottom
  | c_S_inj : forall {x y}, cong_ (ty_term (t_term s_equal [t_term s_succ [x]; t_term s_succ [y]]))
                                  (ty_term (t_term s_equal [x; y]))
  | c_n : forall {x},
            cong_ (ty_term (t_term s_n [x]))
                  (ty_copair
                     (ty_term (t_term s_equal [x; t_term s_zero []]))
                     (ty_exists (ty_pair
                                   (ty_term (t_term s_equal [lift_term x; t_term s_succ [t_var Fin.F1]]))
                                   (ty_term (t_term s_n [t_var Fin.F1]))
                                )
                     )
                  )
  .
  
  Definition cong {n} := @cong_ n.
End Ex2Congruence.

Module Ex2NJ := NJ(Ex2Term)(Ex2Congruence).

Module Q2.
  Import Ex2NJ.

  Theorem Q2 : is_provable (@ty_forall 0 (ty_pair
                                            (ty_arrow
                                               (ty_term (t_term s_n [t_var Fin.F1]))
                                               (ty_term (t_term s_n [t_term s_succ [t_var Fin.F1]]))
                                            )
                                            (ty_arrow
                                               (ty_term (t_term s_n [t_term s_succ [t_var Fin.F1]]))
                                               (ty_term (t_term s_n [t_var Fin.F1]))
                                            )
                                         )
                           ).
  Proof.
    (* eexists. do 3 constructor; simpl. *)
    (* + eapply p_equiv; [ eapply te_sym; eapply te_term; eapply c_n *)
    (*                   | eapply p_copair2; eapply p_exists; eapply p_pair; simpl ]. *)
    (*   eapply p_equiv; [ eapply te_sym; eapply te_term; eapply c_refl | eapply p_tt ]. *)
    (*   eapply p_equiv; [ | eapply p_var with (i:=Fin.F1) ]. *)
    (*   simpl; eapply te_refl. *)
    (* + eapply p_case; [ eapply p_equiv; [| eapply p_var with (i:=Fin.F1) ] *)
    (*                  |  *)
    (*                  | eapply p_pair2; eapply p_ecase; [|] *)
    (*                  ]; simpl. *)
    (*   eapply te_term; eapply c_n. *)
    (*   eapply p_absurd; eapply p_equiv; [| eapply p_var with (i:=Fin.F1) ]. simpl; eapply te_term; eapply c_neq_0. *)
    (*   simpl. eapply p_equiv; [|eapply p_var with (i:=Fin.F1)]. simpl. eapply te_refl. *)
    (*   simpl. eapply p_equiv; [|eapply p_var with (i:=Fin.F1)]. simpl. *)
  Admitted.

End Q2.

Module Ex3Term <: TermDef.
  Inductive symbol_ :=
  | s_p
  .
  Definition symbol := symbol_.
  Theorem eq_symbol_dec : forall (s s' : symbol), {s=s'}+{s<>s'}.
  Proof. decide equality. Qed.
  Fixpoint arity s :=
    match s with
      | s_p => 0
    end.
End Ex3Term.

Module Ex3Congruence <: TermCongruence(Ex3Term).
  Module E := Expr(Ex3Term).
  Import E.
  Export E.
  
  Inductive cong_ {n} : relation (type n) :=
  | c_p : cong_ (ty_term (t_term s_p []))
                (ty_arrow (ty_term (t_term s_p [])) ty_bottom)
  .
  
  Definition cong {n} := @cong_ n.
End Ex3Congruence.

Module Ex3NJ := NJ(Ex3Term)(Ex3Congruence).

Module Q3.
  Import Ex3NJ.
  
  Theorem Q3 : @is_provable 0 ty_bottom.
  Proof.
    eexists.
    eapply p_app; try eapply p_abs; try eapply p_app; try eapply p_var with (i:=Fin.F1);
    simpl; try eapply te_refl.
    eapply te_context_arrow; try apply te_refl.
    eapply te_term. eapply c_p.
    eapply te_term. eapply c_p.
  Qed.
    
End Q3.

Module Q4(T:TermDef)(TC:TermCongruence(T)).
  Module NJ4 := NJ(T)(TC).
  Import NJ4.
  Export NJ4.

  (* TODO : better name *)
  Inductive weak_equiv {n} : type n -> type n -> Prop :=
  | we_atom_l : forall i t, weak_equiv (ty_term (t_var i)) t
  | we_atom_r : forall i t, weak_equiv t (ty_term (t_var i))
  | we_term : forall s xs ys, weak_equiv (ty_term (t_term s xs)) (ty_term (t_term s ys))
  | we_arrow : forall a b c d, weak_equiv (ty_arrow a b) (ty_arrow c d)
  | we_forall : forall a b, weak_equiv (ty_forall a) (ty_forall b)
  | we_exists : forall a b, weak_equiv (ty_exists a) (ty_exists b)
  | we_bottom : weak_equiv ty_bottom ty_bottom
  | we_copair : forall a b c d, weak_equiv (ty_copair a b) (ty_copair c d)
  | we_top : weak_equiv ty_top ty_top
  | we_pair : forall a b c d, weak_equiv (ty_pair a b) (ty_pair c d)
  .

  Definition sans_confusion := forall n p q, p ≡ q -> @weak_equiv n p q.

  Ltac simpl_fold :=
    repeat match goal with
               [ H1 : context[fold_right _ _ nil] |- _ ] => simpl in H1; subst
           end.

  Ltac simpl_nf :=
    match goal with
      | [ H : nfview _ |- _ ] =>
        inversion H; simpl_exist; subst;
        try (solve by inversion);
        match goal with
            [ H0 : Forall nfview ?ns |- _ ] =>
            destruct ns; simpl;
            [ clear H H0
            | solve by inversion
            ]; simpl_fold
        end
      | [ H : nfview _ |- _ ] =>
        inversion H; simpl_exist; subst;
        [ match goal with
              [ H0 : Forall nfview ?ns |- _ ] =>
              destruct ns; simpl_fold; solve by inversion
          end
        |]
      | [ H : nfview (e_app _ _) |- _ ] => apply nfview_app in H
    end.

  Ltac simpl_empty_nf :=
    repeat match goal with
             | [ H : ?x = ?x -> _ |- _ ] =>
               let H0 := fresh "H" in
               assert (H0 : x = x); [ reflexivity | specialize (H H0); clear H0 ]
             | [ H : 1 = 0 -> _ |- _ ] => clear H
             | [ H : 0 = 1 -> _ |- _ ] => clear H
             | [ H : ?a, H0 : ?a -> ?b |- _ ] => specialize (H0 H)
           end.
  
  (* Lemma empty_nf : sans_confusion -> *)
  (*                  (forall n m Γ (e : exp n m) ty (P : Γ ⊢ e ∈ ty), *)
  (*                     n = 0 -> m = 0 -> nfview e -> *)
  (*                     (forall x, e <> e_absurd x) /\ *)
  (*                     (forall x y, e <> e_app x y) /\ *)
  (*                     (forall x y, e <> e_tapp x y) /\ *)
  (*                     (forall x, e <> e_pair1 x) /\ *)
  (*                     (forall x, e <> e_pair2 x) /\ *)
  (*                     (forall x y, e <> e_ecase x y) /\ *)
  (*                     (forall x y z, e <> e_case x y z) /\ *)
  (*                     ty <> ty_bottom *)
  (*                  ). *)
  (* Proof. *)
  (*   Ltac solver := *)
  (*     match goal with *)
  (*       | [ H : sans_confusion, H0 : _ ≡ _ |- _ ] => *)
  (*         (apply H in H0; try (inversion H0; simpl_exist; subst; *)
  (*                              try (apply Fin.case0; trivial; fail); *)
  (*                              try (unfold not; intro A; inversion A; fail); *)
  (*                              fail)) *)
  (*       | [ H0 : appcontext[?x = ?x -> False] |- _ ] => (eapply H0; eauto) *)
  (*       | [ H0 : appcontext[?x _ = ?x _ -> False] |- _ ] => (eapply H0; eauto) *)
  (*       | [ H0 : appcontext[?x _ _ = ?x _ _ -> False] |- _ ] => (eapply H0; eauto) *)
  (*       | [ H0 : appcontext[?x _ _ _ = ?x _ _ _ -> False] |- _ ] => (eapply H0; eauto) *)
  (*     end. *)

  (*   intros H n m Γ e ty P. *)
  (*   induction P; intros; subst; *)
  (*   repeat constructor; *)
  (*   try (intros; unfold not; intro A; inversion A; fail); *)
  (*   try (apply Fin.case0; trivial; fail); *)
  (*   solver; unfold not in *; *)
  (*   try (exfalso; simpl_nf; try inversion H6; simpl_exist; *)
  (*        simpl_empty_nf; destruct_pairs; *)
  (*        match goal with *)
  (*          | [ P : has_type Γ _ _ |- _ ] => *)
  (*            inversion P; simpl_exist; *)
  (*          try (apply Fin.case0; trivial; fail); *)
  (*          repeat solver *)
  (*        end; fail *)
  (*       ); *)
  (*   try ( exfalso; inversion H3; simpl_exist; subst; *)
  (*         destruct ns; simpl_fold; *)
  (*         [ inversion H6 *)
  (*         | destruct ns; inversion H1; simpl_exist; subst; simpl_forall_list; *)
  (*           apply nfview_app in H3; simpl_empty_nf; destruct_pairs; *)
  (*           [ inversion H6; simpl_exist; subst; *)
  (*             try (apply Fin.case0; auto; fail); *)
  (*             try (inversion P1; simpl_exist; subst; try solver; fail); *)
  (*             try solver *)
  (*           | solver *)
  (*           ] *)
  (*         ]; fail). *)
  (* Qed. *)

  (* Theorem sans_confusion_coherent : sans_confusion -> *)
  (*                                   forall (u : exp 0 0), nf u -> [] ⊢ u ∈ ty_bottom -> False. *)
  (* Proof. *)
  (*   intros H u nf p. *)
  (*   apply nf_nfview in nf. *)
  (*   assert (P := empty_nf H _ _ _ _ _ p). *)
  (*   assert (0=0). reflexivity. *)
  (*   specialize (P H0 H0 nf). *)
  (*   destruct_pairs. *)
  (*   apply H8; auto. *)
  (* Qed. *)
  
End Q4.

Module Q5(T:TermDef)(TC:TermCongruence(T)).
  Module NJ5 := Q4(T)(TC).
  Import NJ5.
  Export NJ5.

  Lemma vector_nth_map : forall {n A B} (f : A -> B) (v : Vector.t A n) i,
                           (Vector.map f v)[@i] = f v[@i].
  Proof.
    intros. eapply Vector.nth_map; eauto.
  Qed.
  
  Lemma vector_map_id : forall {n A} (v : Vector.t A n),
                          v = Vector.map (fun x => x) v.
  Proof.
    dependent induction v; simpl; f_equal; auto.
  Qed.

  Lemma vector_map_sur {n A B} (f g : A -> B) (v : Vector.t A n) :
    (forall i, f v[@i] = g v[@i]) ->
    Vector.map f v = Vector.map g v.
  Proof.
    dependent induction v; intros; simpl; auto.
    f_equal.
    specialize (H Fin.F1). auto.
    apply IHv; intros. specialize (H (Fin.FS i)). auto.
  Qed.

  Lemma term_subst_1_lift_term : forall {n} (t : term n) t',
                                   term_subst Fin.F1 t (lift_term t') = t'.
  Proof.
    dependent induction t' using termRect.
    destruct n; auto; apply Fin.case0; auto.
    simpl; f_equal. rewrite (vector_map_id t0); repeat rewrite vector_map_map.
    apply vector_map_sur. intros; eapply H.
  Qed.
    
  Lemma lift_term_term_subst :
    forall {n} i (t : term n) t',
      term_subst (Fin.FS i) (lift_term t) (lift_term t') = lift_term (term_subst i t t').
  Proof.
    dependent induction t' using termRect.
    destruct (eq_fin_dec i t0) eqn:H.
    subst. simpl. repeat rewrite fin_subst_eq. trivial.
    + simpl. assert (H' := fin_subst_neq _ _ _ (lift_term t) t i t0 n0).
      destruct H'. destruct_pairs. rewrite H0. rewrite H1. auto.
    + simpl. f_equal. repeat rewrite vector_map_map.
      apply vector_map_sur. intros. eapply H. apply JMeq_refl.
  Qed.
    
  Lemma lift_type_term_subst :
    forall {n} i (t : term n) ty,
      type_subst (Fin.FS i) (lift_term t) (lift_type ty) = lift_type (type_subst i t ty).
  Proof.
    dependent induction ty; simpl; f_equal; auto using lift_term_term_subst.
  Qed.
    
  Lemma liftΓ_term_subst :
    forall {n m} i (t : term m) (Γ : Vector.t (type (S m)) n),
      Vector.map (type_subst (Fin.FS i) (lift_term t)) (liftΓ Γ) = liftΓ (Vector.map (type_subst i t) Γ).
  Proof.
    intros. dependent induction Γ; simpl; f_equal; auto using lift_type_term_subst.
  Qed.

  Lemma term_subst_comm : forall {n} (t : term n) t' a i,
                            term_subst Fin.F1 (term_subst i t t')
                                       (term_subst (Fin.FS i) (lift_term t) a) =
                            term_subst i t (term_subst Fin.F1 t' a).
  Proof.
    dependent induction a using termRect; intros.
    + destruct (eq_fin_dec (Fin.FS i) t0) eqn:H; subst.
      * simpl. repeat rewrite fin_subst_eq.
        apply term_subst_1_lift_term.
      * dependent destruction t0.
        simpl. repeat rewrite fin_subst_eq. auto.
        simpl. assert (i <> t0); [intro; subst; apply n0; auto|].
        assert (H' := fin_subst_neq _ _ _ (lift_term t) t i t0 H0).
        destruct H'; destruct_pairs. rewrite H1. rewrite H2. simpl.
        destruct n; auto; apply Fin.case0; auto.
    + simpl. f_equal. repeat rewrite vector_map_map.
      apply vector_map_sur; intros. eapply H; eauto.
  Qed.
        
  Lemma type_subst_comm : forall {n} (t : term n) t' a i,
                            type_subst Fin.F1 (term_subst i t t')
                                       (type_subst (Fin.FS i) (lift_term t) a) =
                            type_subst i t (type_subst Fin.F1 t' a).
  Proof.
    dependent induction a; intros; simpl; try (f_equal; eauto using term_subst_comm; fail).
    (* lift_type needs to be replaced by lift_type_by, this is very difficult as n+m is not definitionally equal to m+n... *)
    admit.
    admit.
  Qed.
    
  Theorem has_type_term_subst :
    forall {n m} Γ (u : exp n (S m)) ty i t (P : Γ ⊢ u ∈ ty),
      Vector.map (type_subst i t) Γ ⊢ exp_subst_term i t u ∈ type_subst i t ty.
  Proof.
    intros.
    dependent induction P; simpl;
    try (
        repeat match goal with
                 | [ H : (forall (_ : ?ty), _) |- _ ] =>
                   let x := fresh "x" in
                   evar (x : ty); specialize (H x);
                 match goal with
                   | [ x := ?a : ?b ~= ?c |- _ ] => unify b c; subst x
                   | [ x := _ : _ |- _ ] => subst x
                 end
               end;
        try (
            simpl in *; econstructor; eauto using te_subst;
            repeat match goal with
                     | [ H : ?ty ≡ ?ty' |- _ ] =>
                       match ty with
                         | type_subst _ _ _ => fail
                         | _ => eapply te_subst in H
                       end
                   end;
            eauto using te_subst; fail)).
    + econstructor. erewrite Vector.nth_map; eauto using te_subst.
    + econstructor.
      rewrite liftΓ_term_subst in IHP. eauto.
      eapply te_subst in H. eapply H.
    + econstructor. instantiate (1 := type_subst (Fin.FS i) (lift_term t) p).
      rewrite type_subst_comm. eapply IHP.
      eapply te_subst in H. eapply H.
    + simpl in IHP2. rewrite liftΓ_term_subst in IHP2. rewrite lift_type_term_subst in IHP2.
      econstructor; eauto using te_subst.
      
      Grab Existential Variables.
      eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto.
  Qed.

End Q5.
