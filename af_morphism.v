(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This development is an artifact for a TYPES'2024 submission
    that aims at the presentation of proofs for tools that transfer
    the Almost Full inductive predicate [2] from one relation to
    another relation, using relational morphisms (simple but
    versatile), or the more complex quasi-morphisms for which
    we present both a short proof (in the decidable case), and a
    much more involved proof (using two main tools, see below).

    The quasi-morphism tool came up as a nice abstraction from a
    complete refactoring of our first proof of Kruskal's tree theorem
    in Coq [4], aimed at avoiding the many redundancies present there.
    Both versions follow the outline of Wim Veldman's intuitionistic
    proof [1] (that also contains these redundancies). But in the 
    refactoring, we combine tools that can already be spotted in [1] 
    (or already in [3] btw) but were not abstracted as a standalone
    tool explainable by itself, independently of the context of those
    intricate proofs. This notion of quasi-morphism also explains
    nicely the main overhead to tackle the non-decidable case, which
    is avoided in eg [5] possibly for the reasons that it involves
    both the FAN theorem for inductive bars and a finitary combinatorial
    principle (see eg [1] in proof of thm 7.1 p241). Another reason
    is that the non-decidable case works only with negations free
    formulations of statements.

    This articfact is mostly standalone as it relies only on the 
      - List module of the standard library;
      - and Utf8 for mathematician friendly notations.
    We put a strong effort at getting short and readable proof scripts,
    usually less than 5 loc, and never exceeding 15 loc (excl. comments).
    It is also completely generic in the Prop-bounded vs Type-bounded
    choice for the definition of the af predicate.

    [1] "An intuitionistic proof of Kruskal's tree theorem" W. Veldman, 2004
    [2] "Stop when you are Almost Full" T. Coquand et al., 2012
    [3] "Higman's lemma in type theory" D. Fridlender, 1996 
    [4] https://members.loria.fr/DLarchey/files/Kruskal
    [5] "Higman's Lemma and Its Computational Content" M. Seisenberger et al. 2016
*)

Require Import List Utf8.

Set Implicit Arguments.

(** Reserved Notations are parsing and display rules only,
    the semantics will be defined later.

    The connectives ⊥ₜ, ∨ₜ, ∧ₜ, ∃ₜ and ⇄ₜ with a (.)ₜ
    subscripts are Base-bounded "FOL like" connectives
    where Base can be globally selected as either Prop
    or Type. They are used only for parsing, and not
    for display for reasons explained below. *)

Reserved Notation "⊥ₜ" (at level 0).
Reserved Notation "P ∨ₜ Q" (at level 81, right associativity).
Reserved Notation "P ∧ₜ Q" (at level 80, right associativity).
Reserved Notation "P ⇄ₜ Q" (at level 95, no associativity).
Reserved Notation "∃ₜ x .. y , P" (at level 200, x binder, right associativity).

Reserved Notation "x ∈ l" (at level 70, no associativity, format "x  ∈  l").

Reserved Notation "P ⊆₁ Q" (at level 70, no associativity, format "P  ⊆₁  Q").
Reserved Notation "P ⊆₂ Q" (at level 70, no associativity, format "P  ⊆₂  Q").

Reserved Notation "P ∩₁ Q" (at level 31, left associativity, format "P  ∩₁  Q").
Reserved Notation "P ∩₂ Q" (at level 31, left associativity, format "P  ∩₂  Q").
Reserved Notation "R +₂ T" (at level 31, left associativity, format "R  +₂  T").

Reserved Notation "R ↑ a" (at level 1, left associativity, format "R ↑ a").
Reserved Notation "R ⇈ l" (at level 1, left associativity, format "R ⇈ l").
Reserved Notation "R ⇓ P" (at level 1, no associativity, format "R ⇓ P").
Reserved Notation "P ⤉ l" (at level 1, left associativity, format "P ⤉ l").

(** Prop vs Type global choice:
     - when Base := Prop, you get Prop bounded results
     - when Base := Type, you get Type bounded results

    Notice the subscript (.)ₜ that is used to remind that
    the corresponding "FOL like" operators depend on the
    choice of Base, and to disambiguate from the usual
    Prop-bounded ∃, ∨, ∧ that are also used in here,
    whichever choice is made for Base.

    As a side effet, when Base := Prop, you can simply
    forget the subscript (.)ₜ to interpret the result.

    IF YOU HAVE INITIAL TROUBLES UNDERSTANDING THE (.)ₜ
    NOTATIONS, JUST IGNORE THE (.)ₜ SUBSCRIPT AND READ
    ASSUMING THE CHOICE Base := Prop.

    Notice that those notations are "parsing only"
    and they do not "display" with the (.)ₜ. Otherwise,
    when Base := Prop, the regular ∃ would be captured
    by that notation and we do not want that. *)

Module Prop_bounded.

  (* When Base := Prop, the (.)ₜ connectives are those of Prop (non-informative)
     In that case, "∃ₜ x, P x" is identical to "∃x, P x" (which is a notation
     for "ex P") for P : _ → Base. *)
  Notation Base := Prop (only parsing).
  Notation "⊥ₜ" := False (only parsing) : type_scope.
  Notation "∃ₜ x .. y , P" := (ex (λ x, .. (ex (λ y, P)) ..)) (only parsing) : type_scope.
  Notation "P ∨ₜ Q" := (P ∨ Q) (only parsing) : type_scope.
  Notation "P ∧ₜ Q" := (P ∧ Q) (only parsing) : type_scope.

End Prop_bounded.

Module Type_bounded.

  (* When Base := Type, the (.)ₜ connectives are those of Type (informative).
     In that case, "∃ₜ x, P x" is identical to "{x & P x}" (which is a notation
     for "sigT P") for P : _ → Base. *)
  Notation Base := Type (only parsing).
  Notation "⊥ₜ" :=  Empty_set (only parsing) : type_scope.
  Notation "∃ₜ x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..)) (only parsing) : type_scope.
  Notation "P ∨ₜ Q" := (P + Q)%type (only parsing) : type_scope.
  Notation "P ∧ₜ Q" := (P * Q)%type (only parsing) : type_scope.

End Type_bounded.

(* Here the user can choose whether to compile type Type bounded versions
   or the Prop bounded versions of the results. Thanks to the generic
   notations defined above, the proofs scripts are "exactly the same",
   but the Coq computed proof terms differ of course. *) 
Import Type_bounded (* Prop_bounded (* choose one *) *).

(* derived iff notation for the Base bounded connective *)
Notation "P ⇄ₜ Q" := ((P → Q) ∧ₜ (Q → P))%type (only parsing) : type_scope.

(** Usual notations and hints for lists: 
    { } for arguments denote that they are flagged 
    as implicit, and usually recovered by unfication
    within a given context. Writing eg @cons removes all
    implicit flags. *)

Import ListNotations.
Arguments cons {_}.     (* cons x l is also denoted x::l *)
Arguments app {_}.      (* app l m is also denoted l++m *)
Arguments In {_}.
Infix "∈" := In.        (* we denote list membership In x l with x ∈ l *)

#[local] Hint Resolve in_map in_or_app in_cons in_eq : core.

(** Usual notations for unary or binary relations,
    viewed as Prop bounded predicate. These *do not*
    depend on the choice of Base. *)

Notation rel₁ X := (X → Prop).
Notation "⊥₁" := (λ _, False).
Notation "⊤₁" := (λ _, True).
Notation "P ⊆₁ Q" := (∀ x, P x → Q x).
Notation "P ∩₁ Q" := (λ x, P x ∧ Q x).

Notation rel₂ X := (X → X → Prop).
Notation "⊥₂" := (λ _ _, False).
Notation "⊤₂" := (λ _ _, True).
Notation "P ⊆₂ Q" := (∀ x y, P x y → Q x y).
Notation "P ∩₂ Q" := (λ x y, P x y ∧ Q x y).

(* The direct sum of two binary relations *)
Definition rel_sum₂ {X Y} (R : rel₂ X) (T : rel₂ Y) (p q : X+Y) :=
  match p, q with
  | inl x₁, inl x₂ => R x₁ x₂
  | inr y₁, inr y₂ => T y₁ y₂
  | _     , _      => False
  end.

Notation "R +₂ T" := (rel_sum₂ R T).

(** Restriction of a binary relation R : rel₂ X to
    the sub-type {x | P x} where P : rel₁ X *)

Definition sub_rel X (P : rel₁ X) (R : rel₂ X) : rel₂ {x | P x} :=
  λ x y, R (proj1_sig x) (proj1_sig y).
Arguments sub_rel {X} P R /.   (* the /. controls the simpl tactic *)
Notation "R ⇓ P" := (sub_rel P R).

(** lifting of a relation is the ground notion for inductive AF relations *)

Section lift.

  Variables (X : Type).

  Implicit Type (R T : rel₂ X) (a : X) (l : list X).

  (* Lifting by a single value a *)
  Definition rel_lift R a := λ x y, R x y ∨ R a x.
  Notation "R ↑ a" := (rel_lift R a).

  Fact rel_lift_inc R a : R ⊆₂ R↑a.
  Proof. now left. Qed.

  Fact rel_lift_mono R T a : R ⊆₂ T → R↑a ⊆₂ T↑a.
  Proof. firstorder. Qed.

  Hint Resolve rel_lift_inc rel_lift_mono : core.

  (* Iterated lifting by a list of values l *)
  Fixpoint rel_lift_list R l :=
    match l with
    | []   => R
    | a::l => (R⇈l)↑a
    end
  where "R ⇈ l" := (rel_lift_list R l).

  Fact rel_lift_list_inc R l : R ⊆₂ R⇈l.
  Proof. induction l; simpl; eauto. Qed.

  Hint Resolve rel_lift_list_inc : core.

  Fact rel_lift_list_mono R T l : R ⊆₂ T → R⇈l ⊆₂ T⇈l.
  Proof. induction l; simpl; auto; firstorder. Qed.

  Fact rel_lift_list_In R x y l : R y x → y ∈ l → ∀z, R⇈l x z.
  Proof.
    intro; induction l; intros [] ?; subst; simpl; auto.
    right; eauto.
  Qed.

End lift.

Arguments rel_lift {X} R /.
Arguments rel_lift_list {_}.

Notation "R ↑ x" := (rel_lift R x).
Notation "R ⇈ l" := (rel_lift_list R l).

#[local] Hint Resolve rel_lift_mono rel_lift_inc
                      rel_lift_list_mono
                      rel_lift_list_inc : core.

(** af predicate characterezing AF relations inductively
    Notice that it is Base-bounded, hence either Type- or
    Prop-bounded depending on the global choice. *)

Inductive af {X} (R : rel₂ X) : Base :=
  | af_full : (∀ x y, R x y) → af R
  | af_lift : (∀ a, af (R↑a)) → af R.

#[local] Hint Constructors af : core.

Fact af_mono X (R T : rel₂ X) : R ⊆₂ T → af R → af T.
Proof. intros HT; induction 1 in T, HT |- *; eauto. Qed.

Fact af_inv X (R : rel₂ X) : af R → ∀x, af (R↑x).
Proof. intros []; auto. Qed.

Fact af_map X Y (f : X → Y) (R : rel₂ Y) : af R → af (λ x₁ x₂, R (f x₁) (f x₂)).
Proof.
  induction 1 as [ | R _ IHR ]; eauto.
  constructor 2; intros x.
  apply af_mono with (2 := IHR (f x)); simpl; firstorder.
Qed. 

(** Now come the easy to prove but but versatile to use
    surjective relation morphisms *)

Section af_rel_morph.

  Variables (X Y : Type) (f : X → Y → Prop)
            (R : rel₂ X) (T : rel₂ Y)
            (Hf : ∀y, ∃ₜ x, f x y)          (** f is (strongly) surjective *)
            (HRT : ∀ x₁ x₂ y₁ y₂, f x₁ y₁
                                → f x₂ y₂
                                → R x₁ x₂
                                → T y₁ y₂)  (** f is a morphism form R to S *)
            .

  Theorem af_rel_morph : af R → af T.
  Proof.
    intros H; revert H T HRT.
    induction 1 as [ | R _ IHR ]; intros T HT.
    + constructor 1; intros y1 y2.
      destruct (Hf y1); destruct (Hf y2); eauto.
    + constructor 2; intros y.
      destruct (Hf y) as (x & ?).
      apply (IHR x); firstorder.
  Qed.

End af_rel_morph.

Check af_rel_morph.
Print Assumptions af_rel_morph.

(* A convenient tactic notation to apply af_rel_morph *)
Tactic Notation "af" "rel" "morph" uconstr(g) :=
  match goal with
  |- af _ → af _ => apply af_rel_morph with (f := g)
  end.

(* Trivial using a relational morphism *)
Fact af_af_sub_rel X P (R : rel₂ X) : af R → af R⇓P.
Proof.
  af rel morph (λ x y, x = proj1_sig y).
  + intros []; simpl; eauto.
  + intros ? ? [] [] -> ->; simpl; auto.
Qed.

(* For this one, a morphism will not do. *)
Fact af_full_left X {Y} {R : rel₂ Y} : af R → @af (X+Y) (⊤₂ +₂ R).
Proof.
  induction 1 as [ R HR | R _ IHR ].
  + do 2 (constructor 2; intros []);
      constructor 1; intros [] []; simpl; auto.
  + constructor 2; intros [x|y].
    * constructor 2; intros [x'|y'].
      - constructor 1; intros [] []; simpl; auto.
      - generalize (IHR y'); apply af_mono.
        intros [] []; simpl; tauto.
    * generalize (IHR y); apply af_mono.
      intros [] []; simpl; tauto.
Qed.

(** Remark:

      Showing the more general closure property of AF under direct sums

             af_sum :    af R → af T → af (R +₂ T)

      involves Coquand's constructive version of Ramsey's theorem, ie

             af_inter :  af R → af T → af (R ∩₂ T)

      and this is an "important tool" but it is not necessary in here.
      We just need  af R → af (⊤₂ +₂ R) which is much easier to establish
      as justified above in af_full_left.

      Btw the proof of af_sum (closure under +₂) is obtained via Ramsey by 
      mono(tonicity) and the inclusion (R+₂⊤₂) ∩₂ (⊤₂+₂R) ⊆₂ R+₂T. *)

Section af_lift_vs_af_sub_rel.

  Variables (X : Type) (R : rel₂ X) (a : X).

  (* Relational morphism at play here !! *)
  Fact af_lift_af_sub_rel : af R↑a → af R⇓(λ x, ¬ R a x).
  Proof.
    af rel morph (λ x y, x = proj1_sig y).
    + intros []; simpl; eauto.
    + intros ? ? [] [] -> ->; simpl; tauto.
  Qed.

  Hypothesis Ra_dec : ∀x, R a x ∨ₜ ¬ R a x.

  (* The one below is more complicated as it involves
     building the AF relation 

            ⊤₂⇓(R a) +₂ R⇓(λ x, ¬ R a x)

     but also uses a relational morphism to get 
     a short proof below. *)
  Theorem af_sub_rel_af_lift_dec : af R⇓(λ x, ¬ R a x) → af R↑a.
  Proof.
    intros H.
    generalize (af_full_left (sig (R a)) H).
    af rel morph (λ x y,
      match x with
      | inl x => proj1_sig x = y   (* we cannot factor here because the two *)
      | inr x => proj1_sig x = y   (* proj1_sig are not over the same types  *)
      end).
    + intros y; destruct (Ra_dec y) as [ Hy | Hy ].
      * now exists (inl (exist _ y Hy)).
      * now exists (inr (exist _ y Hy)).
    + intros [[]|[]] [[]|[]] ? ?; simpl; intros <- <-; tauto.
  Qed.

  Hint Resolve af_lift_af_sub_rel af_sub_rel_af_lift_dec : core.

  (* Hence the equivalence in the decidable case *)
  Corollary af_sub_rel_iff_af_lift_dec : af R↑a ⇄ₜ af R⇓(λ x, ¬ R a x).
  Proof. split; auto. Qed.

End af_lift_vs_af_sub_rel.

(** Finiteness (as computable listability) of a unary relation.
    A predicate P : _ → Prop is fin(inite) if one can compute
    a list collecting its span. *)

Definition fin {X} (P : rel₁ X) := {l | ∀x, P x ↔ x ∈ l}.

(* Base-bounded finite choice principles *)

Fact list_choice_Base X (P Q : rel₁ X) (l : list X) :
        (∀x, x ∈ l → P x ∨ₜ Q x)
      → (∀x, x ∈ l → P x) ∨ₜ ∃ₜ x, x ∈ l ∧ₜ Q x.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + left; simpl; tauto.
  + destruct IHl as [ H | (y & ? & ?) ].
    * intros; apply Hl; simpl; auto.
    * destruct (Hl x); simpl; auto.
      - left; intros ? [ <- | ]; auto.
      - right; exists x; simpl; auto.
    * right; exists y; simpl; auto.
Qed.

Arguments list_choice_Base {_}.

Fact fin_choice_Base {X F} (P Q : rel₁ X) :
        fin F
      → (∀x, F x → P x ∨ₜ Q x)
      → F ⊆₁ P ∨ₜ ∃ₜ x, F x ∧ₜ Q x.
Proof.
  intros (l & ?) ?.
  destruct (list_choice_Base P Q l); firstorder.
Qed.

Section af_quasi_morphism_decidable.

  Variables (X Y : Type) (ev : X → Y).

  Notation is_ana y := (λ x, ev x = y).

  Variables (is_ana_fin : ∀y, fin (is_ana y)) (* ev has finite inverse images *)

            (R : rel₂ X) (* abstracts the src embedding *)
            (E : rel₁ X) (* abstracts "exceptional" analyses, eg "has disappointing subtree" *)

            (T : rel₂ Y) (* abstracts the dst embedding *)
            (y₀ : Y)     (* abstracts the tree by which T is lifted *)

            (* ev is a "quasi" morphism from R to T, ie. "up to" E *)
            (ev_qmorph : ∀ x₁ x₂, R x₁ x₂ → T (ev x₁) (ev x₂) ∨ E x₁)

            (* if every analysis of y is exceptional then y must T-embed y0 *)
            (excep_embed : ∀y, is_ana y ⊆₁ E → T y₀ y).

  (** We want to derive: af R → af T↑y₀.

      In this simpler case, we further assume decidability of (T y₀) and E.
      Both T and E are actually defined using a common the source embedding
      (which is not R btw), so in the end their decidability comes from that
      property of the source embeding. But this depends on how T and E are 
      build, so we state the abstract the property here. *)

  Hypothesis (Ty₀_dec : ∀y, T y₀ y ∨ₜ ¬ T y₀ y).
  Hypothesis (E_dec : ∀x, E x ∨ₜ ¬ E x).

  (** ev becomes a surjective rel. morphism {x | ¬ E x} → {y | ¬ T y₀ y}
      that transports af from R⇓(¬ E) to T⇓(¬T y₀). *)

  Theorem af_quasi_morphism_decidable : af R → af T↑y₀.
  Proof.
    intros HR.
    apply af_sub_rel_af_lift_dec with (1 := Ty₀_dec).
    cut (af R⇓(λ x, ¬ E x)); [ | revert HR; apply af_af_sub_rel ].
    af rel morph (λ x y, ev (proj1_sig x) = proj1_sig y).
    + intros (y & Hy).
      assert (∃ₜ x, is_ana y x ∧ₜ ¬ E x) as (x & H1 & H2);
        [ | exists (exist _ x H2); auto ].
      destruct (fin_choice_Base E (λ x, ¬ E x) (is_ana_fin y)) as [ | (? & ? & ?) ]; eauto.
      destruct Hy; eauto.
    + intros [] [] [] []; simpl.
      intros <- <- ?.
      destruct ev_qmorph with (1 := H); tauto.
  Qed.

End af_quasi_morphism_decidable.

Check af_quasi_morphism_decidable.
Print Assumptions af_quasi_morphism_decidable.

(** For the general (non-decidable) case of the Quasi Morphism Theorem, 
    we need many more tools to achieve the proof. Mainly

      - besides extensions of the List library tools (mainly Forall2)
      - list based FANS and finitary combinatorial principle on FANS 
      - the bar inductive predicate and the FAN theorem for inductive bars
      - the inductive good predicate for lists and the equivalence
        between af R and bar (good R) []. *)

(** Extra tools for List.Forall2 *)

#[local] Hint Resolve Forall2_app : core.

Section Forall2_tools.

  Variables (X Y : Type).

  Implicit Types (R T : X → Y → Prop).

  Fact Forall2_mono R T : R ⊆₂ T → Forall2 R ⊆₂ Forall2 T.
  Proof. induction 2; auto. Qed.

  Fact Forall2_equiv R T : (∀ x y, R x y ↔ T x y) → ∀ l m, Forall2 R l m ↔ Forall2 T l m.
  Proof. intros E; split; apply Forall2_mono; intros ? ?; apply E. Qed.

  (* This one is in the stdlib as of Coq 8.17 *)
  Fact Forall2_cons_iff R x y l m : Forall2 R (x::l) (y::m) ↔ R x y ∧ Forall2 R l m.
  Proof.
    split.
    + inversion 1; eauto.
    + intros []; auto.
  Qed.

  Fact Forall2_nil_inv_r R l : Forall2 R l [] ↔ l = [].
  Proof.
    split.
    + now inversion 1.
    + intros ->; auto.
  Qed.

  Fact Forall2_cons_inv_r R l y m : Forall2 R l (y::m) ↔ ∃ x l', l = x::l' ∧ R x y ∧ Forall2 R l' m.
  Proof.
    split.
    + destruct l; inversion 1; eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

  (* Forall2_app_inv_r is already in the stdlib since Coq 8.13 *)

  Fact Forall2_snoc_inv_r R l y m : Forall2 R l (m++[y]) ↔ ∃ l' x, l = l'++[x] ∧ R x y ∧ Forall2 R l' m.
  Proof.
    split.
    + intros (l' & r & ? & (x & ? & -> & ? & ->%Forall2_nil_inv_r)%Forall2_cons_inv_r & ->)%Forall2_app_inv_r; eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

End Forall2_tools.

Fact Forall2_xchg X Y (R : X → Y → Prop) l m : Forall2 R l m ↔ Forall2 (λ y x, R x y) m l.
Proof. split; induction 1; auto. Qed.

Fact Forall2_eq X l m : Forall2 (@eq X) l m ↔ l = m.
Proof.
  split.
  + induction 1; subst; auto.
  + intros []; induction l; simpl; auto.
Qed.

Fact Forall2_map_right X Y Z (R : X → Z → Prop) (f : Y → Z) l m :
      Forall2 R l (map f m) ↔ Forall2 (λ x y, R x (f y)) l m.
Proof.
  split.
  + revert m; induction l as [ | x l IHl ]; intros [ | y m ]; intros H; try (inversion H; fail); auto.
    simpl in H; apply Forall2_cons_iff in H as []; constructor; auto.
  + induction 1; simpl; auto.
Qed.

Fact Forall2_map_left X Y Z (R : Y → Z → Prop) (f : X → Y) l m :
      Forall2 R (map f l) m ↔ Forall2 (λ x z, R (f x) z) l m.
Proof. rewrite Forall2_xchg, Forall2_map_right, Forall2_xchg; tauto. Qed.

(* The FAN of lw is the collection of choice sequences in lw = [w1;...;wn]
   ie, the lists c = [c1;...;cn] such that for any i, ci ∈ wi *)
Notation FAN lw := (λ c, Forall2 (λ x l, x ∈ l) c lw).

(** Explicit construction of the FAN on list (of lists). This is
    just needed to establish finiteness of the FAN. In the Kruskal-Higman
    project, this finiteness property is established using tools of 
    the Kruskal-Finite prject, and avoids the explicit list_prod/list_fan 
    completely. But importing those tools here would be overkill compared
    to the short explicit construction, of which we do not need many
    properties. *)

Section list_prod.

  Variable (X Y Z : Type) (f : X → Y → Z).

  Implicit Types (l : list X) (m : list Y).

  Definition list_prod l m := flat_map (λ x, map (f x) m) l.

  Hint Resolve in_map : core.

  Fact list_prod_spec l m z : z ∈ list_prod l m ↔ ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ m.
  Proof.
    unfold list_prod; rewrite in_flat_map; split.
    + intros (? & ? & (? & <- & ?)%in_map_iff); eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

End list_prod.

Arguments list_prod {X Y Z}.

Section fin_FAN.

  Variable (X : Type).

  Implicit Type (lw : list (list X)).

  Fixpoint list_fan lw :=
    match lw with
    | []    => [[]]
    | w::lw => list_prod cons w (list_fan lw)
    end.

  Lemma list_fan_spec lw c : FAN lw c ↔ c ∈ list_fan lw.
  Proof.
    induction lw as [ | w1 lw IH ] in c |- *; simpl.
    + split.
      * inversion 1; auto.
      * intros [ <- | [] ]; auto.
    + split; intros Hc.
      * destruct c as [ | x c ]; [ inversion Hc | ].
        apply Forall2_cons_iff in Hc as (? & ?%IH).
        apply list_prod_spec; eauto.
      * apply list_prod_spec in Hc as (? & ? & -> & ? & ?%IH); eauto.
  Qed.

  Theorem fin_FAN lw : fin (FAN lw).
  Proof. exists (list_fan lw); apply list_fan_spec. Qed.

End fin_FAN.

(* (* Some examples of explicit FANs *)
Eval compute in list_fan [[0;1];[2;3]].
Eval compute in list_fan [[0;1];[2];[3;4]].
Eval compute in list_fan [[0;1];[];[2;3]]. *)

(** Finitary choice and combinatorial principles, Prop bounded *)

(* The same Ltac proof script as "list_choice_Base" above *)
Lemma list_choice {X} (P Q : X → Prop) l :
        (∀x, x ∈ l → P x ∨ Q x)
      → (∀x, x ∈ l → P x) ∨ ∃x, x ∈ l ∧ Q x.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + now left; simpl.
  + destruct IHl as [ H | (y & ? & ?) ].
    * intros; apply Hl; simpl; auto.
    * destruct (Hl x); simpl; eauto.
      left; intros ? [ [] | ]; auto.
    * right; exists y; simpl; auto.
Qed.

Fact list_choice_cst_left {X} P Q (l : list X) :
        (∀x, x ∈ l → P ∨ Q x) → P ∨ ∀x, x ∈ l → Q x.
Proof. intro; destruct (list_choice Q (λ _, P) l); firstorder. Qed.

Arguments list_choice_cst_left {_}.

(* P ∨ (.) commutes with finite univ. quantification *)
Fact fin_choice_cst_left X F P (Q : X → Prop) :
        fin F → (∀x, F x → P ∨ Q x) → P ∨ ∀x, F x → Q x.
Proof.
  intros (l & Hl) HPQ.
  destruct (list_choice_cst_left P Q l) as [ | H ]; eauto.
  + intros ? ?%Hl; eauto.
  + right; intros ? ?%Hl; auto.
Qed.

(** The proof of this finitary combinatorial principle is by induction
    on lw. We need the finiteness of the FAN to apply fin_choice_cst_left.

    Notice that it would be trivial to establish it using excluded middle.
    Classically (XM+Choice) it holds even for infinitary FANs. *)

Theorem list_combi_principle X (P : rel₁ (list X)) (B : rel₁ X) lw :
        (∀c, FAN lw c → P c ∨ ∃x, x ∈ c ∧ B x)
      → (∃c, FAN lw c ∧ P c) ∨ (∃w, w ∈ lw ∧ ∀x, x ∈ w → B x).
Proof.
  induction lw as [ | w lw IHlw ] in P |- *; intros HPB.
  + destruct (HPB []) as [ | (_ & [] & _) ]; eauto.
  + assert (H: ∀x, x ∈ w → B x ∨ (∀c, FAN lw c → P (x :: c) ∨ (∃y, y ∈ c ∧ B y))).
    1:{ intros x Hx.
        apply fin_choice_cst_left.
        + apply fin_FAN.
        + intros c Hc.
          destruct (HPB (x::c)) as [ | (? & [<- | ] & ?) ]; eauto. }
    apply list_choice in H as [ | (x & ? & [ (c & []) | (m & []) ]%IHlw) ].
    * right; exists w; eauto.
    * left; exists (x::c); eauto.
    * right; exists m; eauto.
Qed.

(** We introduce the bar inductive predicate for lists *)

(* Do not confuse:
   - "monotone" which refers to unary predicates over lists 
   - with "mono" which refers to unary or binary predicates. *)
Notation monotone P := (∀ x l, P l → P (x::l)).

(* Lifting a predicate P : list _ → Prop with a list r *) 
Notation "P ⤉ r" := (λ l, P (l++r)).

Section bar.

  Variable X : Type.

  Implicit Type (P Q : rel₁ (list X)).

  Inductive bar P : list X → Base :=
    | bar_stop l : P l → bar P l
    | bar_next l : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_mono P Q : P ⊆₁ Q → bar P ⊆₁ bar Q.
  Proof. induction 2; eauto. Qed.

  Fact bar_monotone P : monotone P → monotone (bar P).
  Proof. induction 2; eauto. Qed.

  Fact bar_idem P Q : P ⊆₁ bar Q → bar P ⊆₁ bar Q.
  Proof. induction 2; auto. Qed.

  (** Do not confuse this result with Coquand's version
      of Ramsey's theorem because good (R ∩₂ T) is
      NOT THE SAME as good R ∩₁ good T *)
  Fact bar_intersection P Q :
          monotone P → monotone Q
        → ∀l, bar P l → bar Q l → bar (P ∩₁ Q) l.
  Proof. intros ? ?; do 2 induction 1; eauto. Qed.

  Section bar_lifted_ind.

    (** A generalized induction principle for lifted bar 
        predicates, ie of the form (bar P)⤉m *)

    Variable (m : list X) (P : rel₁ (list X)) (Q : list X → Base)
             (HQ1 : P⤉m ⊆₁ Q)
             (HQ2 : ∀l, (∀x, (bar P)⤉m (x::l))
                      → (∀x, Q (x::l))
                      → Q l).

    Local Lemma bar_ind_app v : bar P v → ∀l, l++m = v → Q l.
    Proof.
      induction 1 as [ v Hv | v Hv IHv ]; intros l Hl.
      + subst; auto.
      + apply HQ2; intros x.
        * simpl; now subst.
        * apply (IHv x (_::_)); now subst.
    Qed.

    Hint Resolve bar_ind_app : core.

    Theorem bar_lifted_ind : (bar P)⤉m ⊆₁ Q.
    Proof. simpl; eauto. Qed.

  End bar_lifted_ind.

  (* With bar_app_ind, we get a very simple proof here *)

  Lemma bar_lifted_iff P u v : (bar P)⤉u v ⇄ₜ bar P⤉u v.
  Proof.
    split.
    + apply bar_lifted_ind; eauto.
    + induction 1; eauto.
  Qed.

  Theorem bar_lifted_nil P u : bar P u ⇄ₜ bar P⤉u [].
  Proof. apply bar_lifted_iff with (v := []). Qed.

End bar.

#[local] Hint Constructors bar : core.
Arguments bar {_}.
Arguments bar_intersection {X P Q} _ _ {l}.

Section bar_relmap.

  (** This tool is similar to af_rel_morph but for bar instead of af *)

  Variables (X Y : Type) (f : X → Y → Prop)
            (R : rel₁ (list X)) (T : rel₁ (list Y))
            (Hf : ∀y, ∃ₜ x, f x y)                     (** f is surjective *)
            (HRT : ∀ l m, Forall2 f l m → R l → T m)   (** f is a morphism form R to T *)
            .

  Theorem bar_rel_morph l m : Forall2 f l m → bar R l → bar T m.
  Proof.
    intros H1 H2; revert H2 m H1 T HRT.
    induction 1 as [ l Hl | l Hl IHl ]; intros m H1 T HRT.
    * constructor 1; eauto.
    * constructor 2; intros y.
      destruct (Hf y) as (x & Hx).
      apply (IHl x); auto.
  Qed.

End bar_relmap.

Section bar_map_inv.

  Variables (X Y : Type) (f : X → Y) (P : rel₁ (list Y)).

  Lemma bar_map_inv l : bar P (map f l) → bar (λ m, P (map f m)) l.
  Proof.
    apply bar_rel_morph with (f := λ x y, x = f y); eauto.
    + now intros ? ? ->%Forall2_map_right%Forall2_eq.
    + now rewrite <- Forall2_map_right, Forall2_eq.
  Qed.

End bar_map_inv.

Section FAN_theorem.

  (** That proof of the FAN theorem on inductive bars is derived
      but significantly reworked from Daniel Fridlender's paper

      https://www.brics.dk/RS/98/39/BRICS-RS-98-39.pdf

      which was designed with ACL2.

      In particular, we completely avoid using an explicit
      computation of the FAN like "list_fan" above
      and instead work directly with the FAN predicate.
      Notice the the finiteness of the FAN is not needed
      in this proof, but is needed in the proof of the
      combinatorial principle list_combi_principle. *)

  Variables (X : Type) (P : rel₁ (list X)) (HP : monotone P).

  Local Fact P_monotone_app l m : P m → P (l++m).
  Proof. induction l; simpl; auto. Qed.

  (* P right-lifted by u holds over all choices seqs of lw 
     Notice that when u is [], we simply get FAN lw ⊆₁ P *)
  Let Plift_on_FAN u lw := FAN lw ⊆₁ P⤉u.

  Local Fact Plift_on_FAN_monotone u : monotone (Plift_on_FAN u).
  Proof.
    intros ? ? Hv ? (? & ? & -> & ? & ?%Hv)%Forall2_cons_inv_r.
    now apply HP.
  Qed.

  Hint Resolve P_monotone_app Plift_on_FAN_monotone : core.

  Local Lemma bar_P_bar_Plift_on_FAN {u} : bar P u → bar (Plift_on_FAN u) [].
  Proof.
    induction 1 as [ | u _ IHu ].
    + constructor 1; unfold Plift_on_FAN; simpl; auto.
    + constructor 2; intros w.
      induction w as [ | a w IHw ].
      * constructor 1.
        (* FAN [[]] is empty *)
        intros ? (_ & _ & _ & [] & _)%Forall2_cons_inv_r.
      * (* We combine IHu and IHv using bar_intersection *)
        specialize (IHu a).
        apply bar_lifted_nil in IHw.
        apply bar_lifted_nil.
        generalize (@Plift_on_FAN_monotone (a::u)); intros Hu.
        assert (monotone (Plift_on_FAN u)⤉[w]) as Hw by (simpl; auto).
        generalize (bar_intersection Hu Hw IHu IHw).
        clear Hu Hw IHu IHw; unfold Plift_on_FAN.
        (* The result follows by mono(tonicity) *)
        apply bar_mono.
        intros ? [] ? (? & ? & -> & [ <- | ] & ?)%Forall2_snoc_inv_r; eauto.
        rewrite <- app_assoc; auto.
  Qed.

  (* The FAN theorem for list based FANs
     If a (monotone) P is unavoidable starting from []
     then P is also uniformly unavoidable on FANs starting from [] *)
  Theorem FAN_theorem : bar P [] → bar (λ lw, FAN lw ⊆₁ P) [].
  Proof.
    (* Plift_on_FAN [] is equivalent to λ lw, FAN lw ⊆₁ P *)
    intros H.
    apply bar_mono with (2 := bar_P_bar_Plift_on_FAN H).
    intros ? H1 ? ?%H1; now rewrite <- app_nil_r.
  Qed.

End FAN_theorem.

(** Inductive characterization of good sequences and equivalence
    between af R⇈l and bar (good R) l. In particular, we get
    af R is equivalent to bar good [] *)

Section good.

  Hint Resolve in_or_app in_eq in_cons : core.

  Variable X : Type.

  Implicit Type (R T : rel₂ X).

  (* l = [x1;...;xn] is good iff R xⱼ xᵢ for some i < j *)
  Inductive good R : list X → Prop :=
    | good_stop x y l : y ∈ l → R y x → good R (x::l)
    | good_skip x l : good R l → good R (x::l).

  Hint Constructors good : core.

  (** Basic properties of good *)

  Fact good_monotone R : monotone (good R).
  Proof. apply good_skip. Qed.

  Fact good_mono R T : R ⊆₂ T → good R ⊆₁ good T.
  Proof. induction 2; eauto. Qed.

  Fact good_app_left R l m : good R m → good R (l++m).
  Proof. induction l; simpl; eauto. Qed.

  Fact good_app_right R l m : good R l → good R (l++m).
  Proof. induction 1; simpl; eauto. Qed.

  Fact good_nil_inv R : good R [] ↔ False.
  Proof. split; inversion 1. Qed.

  Fact good_cons_inv R x l :
         good R (x::l) ↔ (∃y, y ∈ l ∧ R y x) ∨ good R l.
  Proof. split; [ inversion 1 | intros [ (? & ? & ?) | ] ]; eauto. Qed.

  Hint Resolve good_app_left good_app_right : core.

  Fact good_app_inv R l m :
       good R (l++m) ↔ good R l ∨ good R m ∨ ∃ x y, x ∈ l ∧ y ∈ m ∧ R y x.
  Proof.
    split.
    + induction l as [ | x l IHl ]; simpl; auto.
      intros [ (y & []%in_app_iff & ?) 
             | [ | [ | (y & z & ? & ? & ?) ] ]%IHl ]%good_cons_inv; eauto.
      * do 2 right; exists x, y; eauto.
      * do 2 right; exists y, z; eauto.
    + intros [ | [ | (? & ? & (? & ? & ->)%in_split & ? & ?) ] ]; eauto.
      rewrite <- app_assoc; simpl; eauto.
  Qed.

  Fact good_snoc R x l y : x ∈ l → R y x → good R (l++[y]).
  Proof. rewrite good_app_inv, good_cons_inv; do 2 right; eauto. Qed.

  Hint Resolve good_snoc : core.

  Fact good_rel_lift_lifted R x : good R↑x ⊆₁ (good R)⤉[x].
  Proof. induction 1 as [ ? ? ? ? [] | ]; simpl; eauto. Qed.

  Hint Resolve good_rel_lift_lifted : core.

  Fact good_rel_lift_list_good_lifted R l : good (R⇈l) ⊆₁ (good R)⤉l.
  Proof.
    induction l as [ | x l IHl ]; simpl; intros m Hm.
    + now rewrite app_nil_r.
    + replace (m++x::l) with ((m++[x])++l); auto.
      now rewrite <- app_assoc.
  Qed.

  (** Now properties of bar good *)

  Local Fact bar_lift_bar_lifted R x : bar (good R↑x) ⊆₁ (bar (good R))⤉[x].
  Proof. induction 1; eauto. Qed.

  Local Fact good_snoc_bar_lift R x : (good R)⤉[x] ⊆₁ bar (good R↑x).
  Proof.
    intros l H.
    constructor 2; intros y; constructor 1.
    apply good_app_inv in H as [ H | [ H | (u & v & H1 & [ <- | [] ] & H3) ] ].
    + constructor 2; revert H; apply good_mono; firstorder.
    + rewrite good_cons_inv, good_nil_inv in H; firstorder.
    + constructor 1 with u; simpl; auto.
  Qed.

  Hint Resolve bar_lift_bar_lifted good_snoc_bar_lift : core.

  Theorem bar_good_lift R x l : bar (good R↑x) l ⇄ₜ (bar (good R))⤉[x] l.
  Proof.
    split; auto.
    revert l; apply bar_lifted_ind; auto.
  Qed.

  Hint Resolve rel_lift_list_In : core.

  Fact good_rel_lift_list_full R l : good R l → ∀ x y, R⇈l x y.
  Proof. induction 1; simpl; eauto. Qed.

  Hint Resolve good_rel_lift_list_full : core.

  (** And now the link between af and (bar good) *)

  Fact bar_good_af R l : bar (good R) l → af (R⇈l).
  Proof. induction 1; auto. Qed.

  Local Lemma af_bar_good_rec T : af T → ∀ R l, T ⊆₂ R⇈l → bar (good R) l.
  Proof.
    induction 1 as [ T HT | T _ IHT ]; intros R l Hl.
    + constructor 2; intro u; constructor 2; intro v.
      constructor 1.
      change (good R ([v;u]++l)).
      apply good_rel_lift_list_good_lifted; eauto.
    + constructor 2; intro x.
      apply (IHT x).
      simpl; firstorder.
  Qed.

  Hint Resolve af_bar_good_rec : core.

  Lemma af_bar_good R l : af R⇈l → bar (good R) l.
  Proof. eauto. Qed.

  Hint Resolve bar_good_af af_bar_good : core.

  Theorem af_iff_bar_good R l : af R⇈l ⇄ₜ bar (good R) l.
  Proof. eauto. Qed.

  Corollary af_iff_bar_good_nil R : af R ⇄ₜ bar (good R) [].
  Proof. apply af_iff_bar_good with (l := []). Qed.

End good.

Arguments good {X}.
#[local] Hint Constructors good : core.

(** We conclude with the quasi morphism result, here in the
    general setting where we do not assume decidability 
    properties for T and E. *)

Section af_quasi_morphism.

  Variables (X Y : Type) (ev : X → Y).

  Notation is_ana y := (λ x, ev x = y).

  Variables (is_ana_fin : ∀y, fin (is_ana y))
            (R : rel₂ X) (E : rel₁ X) (T : rel₂ Y) (y₀ : Y)
            (ev_qmorph : ∀ x₁ x₂, R x₁ x₂ → T (ev x₁) (ev x₂) ∨ E x₁)
            (excep_embed : ∀y, is_ana y ⊆₁ E → T y₀ y).

  (** We want to derive: af R → af T↑y₀
      We deal with the general case where
      neither T↑y₀ nor E is assumed decidable *)

  (* First we get the ana(lysis) has a list of inverse images by ev *)

  Let ana y := proj1_sig (is_ana_fin y).

  Local Fact ana_spec x y : ev x = y ↔ x ∈ ana y.
  Proof. apply (proj2_sig (is_ana_fin _)). Qed.

  (* Hence map ev (ana y) = [y] and on the FAN ... *) 
  Local Fact FAN_analysis_eq lx ly : FAN (map ana ly) lx ↔ map ev lx = ly.
  Proof.
    rewrite Forall2_map_right, <- Forall2_eq, Forall2_map_left.
    apply Forall2_equiv; intros ? ?; rewrite ana_spec; tauto.
  Qed.

  (* If a list is R-good then its evaluation is T-good unless it meets E 
     This extends the ev_qmorph property to good sequences *)
  Local Fact ev_good_or_exceptional lx :
         good R lx → good T (map ev lx) ∨ ∃x, x ∈ lx ∧ E x.
  Proof.
    induction 1 as [ t2' t1' l H1 H2 | t1' l H IH ]; simpl.
    + destruct ev_qmorph with (1 := H2); eauto.
    + destruct IH as [ | (? & ? & ?) ]; simpl; eauto.
  Qed.

  (* A(nalyses) W(ell): all possible choice sequences of analyses of ly are good *)
  Let AW ly := FAN (map ana ly) ⊆₁ good R.

  (* The critical proof step: if ly Analyses Well then ly++[y₀] is good for T *)
  Local Lemma AW_good_lifted : AW ⊆₁ (good T)⤉[y₀].
  Proof.
    intros ly Hly; red in Hly.
    destruct list_combi_principle
      with (P := λ l, good T (map ev l))
           (B := E) (lw := map ana ly)
      as [ (lx & H1 & H2) | (a & H1 & H2) ].
    + (* Hypothesis for combi principle *)
      now intros lx Hlx%Hly%ev_good_or_exceptional.
    + (* there is (choice) sequence of analyses lx of ly which maps
         to a good sequence, but lx maps to ly hence ly is good *)
      apply FAN_analysis_eq in H1 as <-.
      now apply good_app_right.
    + (* there is an evaluation in ly of which all analyses are exceptional *)
      apply in_map_iff in H1 as (y & <- & H1).
      apply good_snoc with y, excep_embed; auto.
      now intros ? ?%ana_spec%H2.
  Qed.

  (* The previous results lifted to bar *)
  Local Corollary bar_AW_good_lifted : bar AW ⊆₁ (bar (good T))⤉[y₀].
  Proof.
    intros ly Hly; apply bar_lifted_iff.
    revert Hly; apply bar_mono, AW_good_lifted.
  Qed.

  Hypothesis (HR : af R).

  (* The bar formulation for the FAN theorem below *)
  Local Fact bar_goodR_nil : bar (good R) [].
  Proof. now apply af_iff_bar_good_nil. Qed.

  Hint Resolve good_skip bar_goodR_nil : core.

  (* By the FAN theorem, since R is af, all sequences
     will uniformly analyse well *)
  Local Lemma bar_AW_nil : bar AW [].
  Proof.
    apply bar_map_inv with (P := λ lw, FAN lw ⊆₁ good R),
          FAN_theorem; auto.
  Qed.

  Theorem af_quasi_morphism : af T↑y₀.
  Proof.
    apply af_iff_bar_good_nil, bar_good_lift,
          bar_AW_good_lifted, bar_AW_nil.
  Qed.

End af_quasi_morphism.

Check af_quasi_morphism.
Print Assumptions af_quasi_morphism.








