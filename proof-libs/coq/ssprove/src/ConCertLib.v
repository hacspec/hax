Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith List.
Import List.ListNotations.

Import choice.Choice.Exports.

Open Scope Z_scope.

From Hacspec Require Import Hacspec_Lib_Pre.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

From ConCert.Execution Require Import Serializable.

Program Definition serialize_by_other {A B} (f_to : B -> A) (f_from : A -> B)  `(forall m, f_from (f_to m) = m) `{Serializable A} : Serializable B :=
  {|
      serialize m := serialize (f_to m);
      deserialize m := option_map f_from (deserialize m) ;
  |}.
Next Obligation.
  intros. hnf. rewrite deserialize_serialize.
  unfold option_map. now f_equal.
Defined.

Program Definition serialize_by_other_option {A B} (f_to : B -> Datatypes.option A) (f_from : Datatypes.option A -> Datatypes.option B)  `(forall m, f_from (f_to m) = Some m) `{Serializable A} : Serializable B :=
  {|
      serialize m := serialize (f_to m);
    deserialize m := match (deserialize m) with
                     | Some m => f_from m
                     | None => None
                     end;
  |}.
Next Obligation.
  intros. hnf. simpl. rewrite deserialize_serialize. now f_equal.
Defined.

#[global] Instance hacspec_int_serializable {ws : wsize} : Serializable (int ws) := serialize_by_other (unsigned) (@repr ws) (@wrepr_unsigned ws).

Lemma eqtype_ord_ext :
  forall n, forall x y : fintype.ordinal n, (@eqtype.eq_op
        (fintype_ordinal__canonical__eqtype_Equality
           _ (* (@ord.Ord.clone _ *)
           (*    (ord.ordinal_ordType n) *)
           (*    _ *)
           (*    id) *)) x y) = (@eqtype.eq_op ssrnat.Datatypes_nat__canonical__eqtype_Equality (nat_of_ord x) (nat_of_ord y)).
Proof.
  intros.
  destruct x.
  simpl.
  destruct y.
  simpl.
  reflexivity.
Qed.

Theorem lift_set_commute :
  forall {A : choice_type} {len} (a : nseq_ A (S len)) (b : fintype.ordinal (S len)) (c : A),
    @lift_nseq A (S _) (fmap.setm a b c) =
      fmap.setm (@lift_nseq A (S _) a) (lift_ordinal _ b) c.
Proof.
  clear ; intros ; fold chElement in *.
  simpl in b.
  unfold lift_nseq.
  apply fmap.eq_fmap. intros x ; simpl in x.
  rewrite fmap.setmE.
  unfold fmap.getm.
  simpl fmap.FMap.fmval.
  destruct a ; induction fmval ; simpl lift_fval.
  - now rewrite (lift_fval_equation_2 _ (len) (b, c) nil).
  - {
      destruct x , b.
      rewrite (eqtype_ord_ext (S (S (len)))).
      simpl eqtype.eq_op.
      destruct eqtype.eq_op eqn:eq_o at 2.
      + apply (ssrbool.elimT eqtype.eqP) in eq_o.
        subst.
        destruct ord.Ord.lt.
        * simpl.
          rewrite (lift_fval_equation_2 _ (len)).
          simpl.
          rewrite (eqtype_ord_ext (S (S ( len)))).
          simpl.
          rewrite eqtype.eq_refl.
          reflexivity.
        * rewrite (eqtype_ord_ext (S (len))).
          simpl.
          set (eqtype.eq_op _ _).
          destruct b eqn:eq_b_o ; subst b.
          -- apply (ssrbool.elimT eqtype.eqP) in eq_b_o.
             subst.
             rewrite (lift_fval_equation_2 _ (len)).
             simpl.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             rewrite eqtype.eq_refl.
             reflexivity.
          -- rewrite (lift_fval_equation_2 _ (len)).
             simpl.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             destruct (fst _).
             simpl in *.
             rewrite ssrnat.eqSS.
             rewrite eq_b_o.

             rewrite IHfmval.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             rewrite eqtype.eq_refl.
             reflexivity.

             (* apply (path_sorted_tl _). *)
             {
               intros.
               destruct fmval. reflexivity.
               - cbn.
                 cbn in i.
                 destruct (seq.unzip1 fmval).
                 + reflexivity.
                 + cbn in i.
                   now rewrite LocationUtility.is_true_split_and in i.
             }
      + destruct ord.Ord.lt.
        * simpl.
          rewrite (lift_fval_equation_2 _ (len)).
          simpl.
          rewrite (eqtype_ord_ext (S (S (len)))).
          simpl.
          rewrite eq_o.
          reflexivity.
        * rewrite (eqtype_ord_ext (S (len))).
          simpl.
          set (eqtype.eq_op _ _).
          destruct b eqn:eq_b_o ; subst b.
          -- apply (ssrbool.elimT eqtype.eqP) in eq_b_o.
             subst.
             rewrite (lift_fval_equation_2 _ (len)).
             simpl.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             rewrite eq_o.
             rewrite (lift_fval_equation_2 _ (len)).
             simpl.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             unfold lift_ordinal.
             destruct (fst _).
             simpl.
             simpl in eq_o.
             rewrite eq_o.
             reflexivity.
          -- rewrite (lift_fval_equation_2 _ (len)).
             simpl.
             rewrite (eqtype_ord_ext (S (S (len)))).
             simpl.
             destruct a.
             destruct s.
             simpl in *.
             set (b := eqtype.eq_op _ _) ; destruct b eqn:eq_m_o ; subst b.
             ++ apply (ssrbool.elimT eqtype.eqP) in eq_m_o.
                subst.
                rewrite (lift_fval_equation_2 _ (len)).
                simpl.
                rewrite (eqtype_ord_ext (S (S (len)))).
                simpl.
                now rewrite eqtype.eq_refl.
             ++ rewrite IHfmval.
                rewrite (eqtype_ord_ext (S (S (len)))).
                simpl.
                rewrite eq_o.
                rewrite (lift_fval_equation_2 _ (len)).
                simpl.
                rewrite (eqtype_ord_ext (S (S (len)))).
                simpl.
                rewrite eq_m_o.
                reflexivity.
                (* apply (path_sorted_tl _). *)
                {
                  intros.
                  destruct fmval. reflexivity.
                  - cbn.
                    cbn in i.
                    destruct (seq.unzip1 fmval).
                    + reflexivity.
                    + cbn in i.
                      now rewrite LocationUtility.is_true_split_and in i.
                }
    }
Qed.

Theorem array_from_list_helper_inverse : forall {A} len (m : nseq_ A (S len)),
    array_from_option_list_helper
      (nseq_hd_option m)
      (array_to_option_list (nseq_tl m)) len = m.
Proof.
  intros.
  induction len.
  - unfold nseq_tl.
    unfold nseq_hd_option.
    rewrite array_to_option_list_equation_1.
    destruct m, fmval.
    + now apply fmap.eq_fmap.
    + apply fmap.eq_fmap. intros x ; simpl in x.

      unfold fmap.getm at 2 ; simpl.
      destruct (fst _), m ; [ | discriminate ] ; simpl.
      rewrite array_from_option_list_helper_equation_1.
      unfold setm_option.
      rewrite fmap.setmE.
      now destruct x , m ; [ | discriminate ] ; simpl.
  - rewrite array_to_option_list_equation_2.

    assert (forall (T : ordType) (S : choice_type)
         (m : @fmap.FMap.fmap_of T S
                (ssreflect.Phant (Ord.Ord.sort T -> S)))
         (k : Ord.Ord.sort T) (v : chOption S) (k' : Ord.Ord.sort T),
       @fmap.getm T S (setm_option m k v) k' =
         match v with
         | Some v => @fmap.getm T S (fmap.setm m k v) k'
         | None => @fmap.getm T S m k'
         end) by now destruct v.

    rewrite array_from_option_list_helper_equation_3.
    rewrite (IHlen (nseq_tl m)).

    clear.

    apply fmap.eq_fmap.
    intros x ; simpl in x.
    destruct m ; induction fmval.
    + now unfold fmap.getm ; cbn ; rewrite lift_fval_equation_1.
    + {
        specialize (IHfmval (path_sorted_tl i)).
        unfold nseq_hd_option in *.
        simpl.
        destruct a.
        destruct s.
        unfold fmap.getm at 2.
        simpl.
        destruct m.
        {
          setoid_rewrite <- IHfmval ; clear.

          setoid_rewrite fmap.setmE.
          rewrite !(eqtype_ord_ext (S (S len))).
          simpl eqtype.eq_op.
          replace (_ - _)%nat with O by (set (temp := nseq_tl _) ; rewrite <- (array_to_length_option_list_is_len A len temp) at 1; now rewrite Nat.sub_diag).

          destruct x , m ; [ reflexivity | ].
          rewrite tl_fmap_equation_2.
          unfold setm_option.
          destruct fmval ; [reflexivity | ].
          simpl.
          destruct p, s.
          simpl.
          destruct m0 ; [ discriminate | ].

          rewrite tl_fmap_equation_3.

          unfold fmap.getm.
          simpl.

          set (@fmap.getm_def _ _).
          set (lift_fval _).
          set (lift_fval _).
          assert (l = l0) ; [ subst l l0 | now rewrite H ].
          f_equal.

          now apply lower_fval_ext_list.
        }
        {
          setoid_rewrite <- IHfmval ; clear.
          unfold setm_option.
          unfold fmap.getm.
          simpl.

          rewrite tl_fmap_equation_3.
          destruct (eqtype.eq_op _ _) eqn:eq_o.
          - apply (ssrbool.elimT eqtype.eqP) in eq_o.
            rewrite eq_o.

            subst.
            simpl.

            rewrite lower_fval_equation_2.
            rewrite lift_fval_equation_2.
            simpl.

            rewrite !(eqtype_ord_ext (S (S len))).
            simpl.
            rewrite eqtype.eq_refl.
            reflexivity.
          - unfold setm_option.
            destruct fmval.
            + (* discriminate. *)
              rewrite tl_fmap_equation_1.
              simpl.

              rewrite lower_fval_equation_2.
              rewrite lift_fval_equation_2.
              simpl.

              rewrite lower_fval_equation_1.
              simpl.

              rewrite !(eqtype_ord_ext (S (S len))).
              simpl.
              rewrite !(eqtype_ord_ext (S (S len))) in eq_o.
              simpl in eq_o.
              rewrite eq_o.
              simpl.
              reflexivity.
            + destruct p , s.
              destruct m0 ; [ discriminate | ].
              simpl.

              rewrite lower_fval_equation_2.
              rewrite lift_fval_equation_2.
              simpl.

              rewrite lower_fval_equation_2.
              rewrite lift_fval_equation_2.
              simpl.

              rewrite tl_fmap_equation_3.
              simpl.

              rewrite lower_fval_equation_2.
              rewrite lift_fval_equation_2.
              simpl.

              rewrite !(eqtype_ord_ext (S (S len))).
              simpl.

              rewrite (eqtype_ord_ext (S (S len))) in eq_o.
              simpl in eq_o.
              rewrite eq_o.

              apply (ssrbool.elimF eqtype.eqP) in eq_o.

              destruct (eqtype.eq_op _ _) eqn:eq_o2 ; [ reflexivity | ].


              simpl.

              set (@fmap.getm_def _ _).
              set (lift_fval _).
              set (lift_fval _).
              assert (l = l0) ; [ subst l l0 | now rewrite H ].
              f_equal.
              apply lower_fval_ext_list.
              apply (path_sorted_tl (path_sorted_tl i)).
              apply (path_sorted_tl (path_sorted_tl i)).
              reflexivity.
        }
      }
Qed.

Theorem array_from_list_to_list_unit : forall {A} len (m : nseq_ A len),
    array_from_option_list' (array_to_option_list m) len = m.
Proof.
  intros.
  induction len.
  - now destruct m. (* unit element equailty *)
  - simpl.
    pose (resize_to_length_idemp (array_to_option_list m)).
    rewrite (array_to_length_option_list_is_len A (S len) m) in e.
    rewrite <- e ; clear e.
    rewrite array_to_option_list_equation_2.
    specialize (IHlen (nseq_tl m)).
    apply array_from_list_helper_inverse.
Qed.

Definition defaulted_nseq {A len} (m : nseq_ A (S len)) :=
  forall i, match fmap.getm m i with
       | Some x => x <> chCanonical A
       | None => True
       end.

#[global] Instance nseq_serializable {A : choice_type} {len} `{Serializable A} : Serializable (nseq_ A len) :=
  serialize_by_other (array_to_option_list) (fun x => array_from_option_list' x len) (array_from_list_to_list_unit len).

Ltac serialize_enum := intros ; autounfold ; repeat apply @product_serializable ; fold chElement.

From ConCert.Execution Require Import Blockchain.

#[global] Instance BaseTypes : ConCert.Execution.Blockchain.ChainBase :=
  {|
    Address := nat;
    address_eqb := Nat.eqb ;
    address_eqb_spec := Nat.eqb_spec;
    address_is_contract := Nat.even;
  |}.

From Hacspec Require Import ChoiceEquality.
(* From Hacspec Require Import Hacspec_Lib. *)

Theorem both_ext_prog :
  forall {L I A} (x y : both L I A), both_prog x = both_prog y <-> x = y.
Proof.
  intros L I A [both_x valid_x eq_x] [both_y valid_y eq_y] ; simpl.
  split.
  - intros ; subst.
    f_equal ; easy.
  - easy.
Qed.

Print pkg_core_definition.typed_raw_function.

Instance serializable_code {L I} {A : choice_type} `{Serializable A} : Serializable (pkg_core_definition.code L I A).
Proof.
Admitted.

Instance serializable_both {L I} {A : choice_type} `{Serializable A} : Serializable (both L I A).
Proof.
  (* refine {| serialize *)
  (*             '{| both_prog := *)
  (*                {| *)
  (*                  is_state := is_state; *)
  (*                  is_pure := is_pure *)
  (*                |} ; *)
  (*                both_prog_valid := *)
  (*                {| *)
  (*                  is_valid_code := is_valid_code ; *)
  (*                  is_valid_both := is_valid_both *)
  (*                |} ; *)
  (*                p_eq := p_eq |} := *)
  (*          serialize *)
  (*            (is_pure, *)
  (*              {| *)
  (*                pkg_core_definition.prog := is_state; *)
  (*                pkg_core_definition.prog_valid := is_valid_code |}, *)
  (*              is_valid_both, *)
  (*              p_eq) ; *)
  (*          deserialize x := *)
  (*            option_map (fun y => solve_lift ret_both y) (deserialize x) *)
  (*        |}. *)
  (* Unshelve. *)
  (* 2:{ *)
  (*   eapply product_serializable. *)
  (*   Unshelve. *)
  (*   eapply product_serializable. *)
  (*   Unshelve. *)
  (*   simpl. *)
  (*   eapply product_serializable. *)
  (*   Unshelve. *)
  (* } *)

  (* eapply (@serialize_by_other *)
  (*           (A * pkg_core_definition.code L I A * valid_both) *)
  (*           (both L I A) *)
  (*           (fun x => (is_pure x, {| pkg_core_definition.prog := is_state x; pkg_core_definition.prog_valid := is_valid_code (both_prog_valid x) |})) *)
  (*           (fun '(z , {| pkg_core_definition.prog := y ; pkg_core_definition.prog_valid := x |}) => *)
  (*              _ *)
  (*        )). *)
  (* Unshelve. *)
  (* 3:{ *)
  (*   epose {| is_pure := z ; is_state := y |}. *)
  (*   assert (y = is_state r) by reflexivity. *)
  (*   rewrite H0 in *. *)
  (*   eapply {| *)
  (*     both_prog := r ; *)
  (*     both_prog_valid := {| is_valid_code := x |} *)
  (*   |}. *)
  (* } *)

  (* intros. *)
  (* destruct m. *)
  (* apply both_ext_prog. *)
  (* simpl. *)
  (* destruct both_prog. *)
  (* simpl. *)
  (* reflexivity. *)
  (* apply product_serializable. *)
  (* Unshelve. *)

  (* - apply y. *)
  (* - destruct y. *)
  (*   simpl. *)
  (*   destruct prog. *)
  (*   simpl. *)
  (*   eapply both_valid_ret. *)

  (* apply both *)

Admitted.
