(** * HoTT-light
 ** A lightweight version of the Homotopy Type Theory library prelude. *)

Require Export Unicode.Utf8.
Require Import Coq.Program.Tactics Setoid.
Require Import Relations.
Require Import Equations.Equations.

(** Switches to constants in Type *)
Require Import ConstantsType.

Import Init.
Set Warnings "-notation-overridden".
Import Id_Notations.
Import Sigma_Notations.
Set Warnings "-deprecated-option".
Set Universe Polymorphism.
Set Primitive Projections.

(** We want our definitions to stay transparent. *)
Set Equations Transparent.

Polymorphic Definition transport_r (A : Type) (x : A) (P : A → Type) : P x → ∀ y : A, y = x → P y.
Proof. intros Px y e. apply id_sym in e. destruct e. exact Px. Defined.

Polymorphic Definition transport_dep_r (A : Type) (x : A) (P : forall y : A, y = x → Type) :
  P x id_refl → ∀ (y : A) (e : y = x), P y e.
Proof. intros Px y e. destruct e. apply Px. Defined.

Set Implicit Arguments.

Definition id {A : Type} (a : A) : A := a.

Section TypeEq.

  Equations eq_sym (A : Type) (x y : A) (eq : Id x y) : Id y x :=
  eq_sym id_refl := id_refl _.

  Equations eq_trans (A : Type) (x y z : A) (eq1 : Id x y) (eq2 : Id y z) : Id x z :=
  eq_trans id_refl id_refl := id_refl _.
End TypeEq.

Arguments Id {A} _ _.
Arguments id_refl {A} [a].

Require Import CRelationClasses CMorphisms.

Instance id_reflexive A : Reflexive (@Id A).
Proof. exact (@id_refl A). Defined.

Instance eq_symmetric A : Symmetric (@Id A).
Proof. exact (@eq_sym A). Defined.

Instance eq_transitive A : Transitive (@Id A).
Proof. exact (@eq_trans A). Defined.

Notation " x = y " := (@Id _ x y).
Notation " x = y " := (@Id _ x y) : type_scope.

Inductive prod (A B : Type) := pair : A -> B -> prod A B.

Notation " X * Y " := (prod X Y) : type_scope.
Notation " ( x , p ) " := (@pair _ _ x p).

Equations fst {A B} (p : A * B) : A :=
fst (pair a b) := a.
Transparent fst.

Equations snd {A B} (p : A * B) : B :=
snd (pair a b) := b.
Transparent snd.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Equations ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
ap f id_refl := id_refl.
Transparent ap.

Equations transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
transport P id_refl u := u.
Transparent transport.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Notation "1" := id_refl : equations_scope.
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p ^" (at level 3, format "p '^'").
Notation "p ^" := (eq_sym p%equations) : equations_scope.

Equations apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  p # f x = f y :=
apd f id_refl := id_refl.

(** A typeclass that includes the data making [f] into an adjoin equivalence*)

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B}%type_scope f%function_scope {_} _.
Arguments eissect {A B}%type_scope f%function_scope {_} _.
Arguments eisadj {A B}%type_scope f%function_scope {_} _.
Arguments IsEquiv {A B}%type_scope f%function_scope.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Bind Scope equiv_scope with Equiv.

Reserved Infix "<~>" (at level 85).
Notation "A <~> B" := (Equiv A B) (at level 85) : type_scope.

Notation "f ^^-1" := (@equiv_inv _ _ f _) (at level 3).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) 
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.


(* This definition has slightly changed: the match on the Id is external
   to the function. *)
Equations apD10 {A} {B : A -> Type} {f g : forall x, B x} (h : f = g) : f == g :=
apD10 id_refl := fun h => id_refl.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Axiom funext : Funext.
Existing Instance funext.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^^-1.

Open Scope equations_scope.

Unset Implicit Arguments.
Arguments sigmaI {A} {B}.

Equations path_sigma {A : Type} (P : A -> Type) (u v : sigma A P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v :=
path_sigma _ (sigmaI _ _) (sigmaI _ _) 1 1 := 1.

Equations path_prod_uncurried {A B : Type} (z z' : A * B)
           (pq : (fst z = fst z') * (snd z = snd z')): z = z' :=
path_prod_uncurried (_, _) (_, _) (1, 1) := 1.

Definition path_prod {A B : Type} (z z' : A * B) (e : fst z = fst z') (f : snd z = snd z') : z = z' :=
  path_prod_uncurried _ _ (e, f).

Equations path_prod_eq {A B : Type} (z z' : A * B) (e : fst z = fst z') (f : snd z = snd z') : z = z' :=
path_prod_eq (_, _) (_, _) 1 1 := 1.

Equations eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _ (ap fst p) (ap snd p) = p :=
eta_path_prod (z:=(pair _ _)) id_refl := id_refl.

Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (pair x y) (pair x' y') p q.

Equations ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p :=
ap_fst_path_prod (z:=(pair _ _)) (z':=(pair _ _)) id_refl id_refl := id_refl.

Equations ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q :=
ap_snd_path_prod (z:=(_, _)) (z':=(_, _)) id_refl id_refl := id_refl.

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z').
Proof.
  unshelve refine (BuildIsEquiv _ _ _).
  - exact (fun r => (ap fst r, ap snd r)).
  - intro ; apply eta_path_prod.
  - intros [p q]. exact (path_prod'
                          (ap_fst_path_prod p q)
                          (ap_snd_path_prod p q)). 
  - destruct z as [x y], z' as [x' y'].
    intros [p q]; simpl in p, q.
    destruct p, q; apply id_refl.
Defined.

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.
Arguments center A {Contr}.

Global Instance contr_forall A {P : A -> Type} {H : forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => @center _ (H a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

Equations concat {A} {x y z : A} (e : x = y) (e' : y = z) : x = z :=
concat id_refl q := q.
Notation "p @ q" := (concat p q).

Definition moveR_E A B (f:A -> B) {H : IsEquiv f} (x : A) (y : B) (p : x = f^^-1 y)
  : (f x = y)
  := ap f p @ (@eisretr _ _ f _ y).

Lemma contr_equiv A B (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  eapply moveR_E.
  apply contr.
Qed.

Equations concat_1p {A : Type} {x y : A} (p : x = y) :
  id_refl @ p = p :=
concat_1p id_refl := id_refl.

Equations concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ id_refl  = p :=
concat_p1 id_refl := id_refl.

Equations concat_Vp {A : Type} {x y : A} (p : x = y) :
  eq_sym p @ p = id_refl :=
concat_Vp id_refl := id_refl.

Equations concat_pV {A : Type} {x y : A} (p : x = y) : p @ eq_sym p = id_refl :=
concat_pV id_refl := id_refl.

Equations concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
concat_p_pp id_refl _ _ := id_refl.

Hint Rewrite @concat_p1 @concat_Vp @concat_pV : concat.

Instance Id_equiv A :
  Equivalence (@Id A) := {}.

Instance concat_morphism (A : Type) x y z :
  Proper (Id ==> Id ==> Id) (@concat A x y z).
Proof. reduce. destruct X. destruct X0. destruct x0. reflexivity. Defined.

Definition trans_co_eq_inv_arrow_morphism@{i j k} :
  ∀ (A : Type@{i}) (R : crelation@{i j} A),
    Transitive R → Proper@{k j} (respectful@{i j k j k j} R
    (respectful@{i j k j k j} Id (@flip@{k k k} _ _ Type@{j} arrow))) R.
Proof. reduce. transitivity y. assumption. now destruct X1. Defined.
Existing Instance trans_co_eq_inv_arrow_morphism.

Equations concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
    (r @ p x) @ ap g q = (r @ q) @ p y :=
concat_pp_A1 _ id_refl id_refl := concat_p1 _.

Equations whiskerL {A : Type} {x y z : A} (p : x = y)
           {q r : y = z} (h : q = r) : p @ q = p @ r :=
whiskerL _ id_refl := id_refl.

Equations whiskerR {A : Type} {x y z : A} {p q : x = y}
           (h : p = q) (r : y = z) : p @ r = q @ r :=
whiskerR id_refl _ := id_refl.

Equations moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_sym q @ p = id_refl -> p = q :=
moveL_M1 _ id_refl := fun e => e.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
: eq_sym p = eq_sym q := ap (@eq_sym _ _ _) h.

Equations ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q :=
ap02 f id_refl := id_refl.

Equations ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q) :=
ap_p_pp f _ id_refl _ := concat_p_pp _ id_refl _.

Equations ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p) :=
ap_compose f g id_refl := id_refl.

Equations concat_A1p {A : Type} {g : A -> A} (p : forall x, g x = x) {x y : A} (q : x = y) :
  (ap g q) @ (p y) = (p x) @ q :=
concat_A1p (g:=g) p (x:=x) 1 with p x, g x :=
  { concat_A1p p 1 1 _ := 1 }.

Ltac remember_let H ::=
  lazymatch goal with
  | [ H := ?body : ?type |- _ ] => generalize (id_refl : H = body)
  end.

Notation " 'rew' H 'in' c " := (@Id_rect_r _ _ _ c _ H) (at level 20).
Notation " 'rewd' H 'in' c " := (@Id_rect_dep_r _ _ _ c _ H) (at level 20).

Ltac unfold_packcall packcall ::=
  lazymatch goal with
    |- ?x = ?y -> ?P =>
    let y' := eval unfold packcall in y in
        change (x = y' -> P)
  end.

(** Singletons are contractible! *)
Derive NoConfusion for Id.

Next Obligation.
  destruct X. destruct a0. destruct pr2. reflexivity.
Defined.

Next Obligation.
  destruct a0, b. destruct pr2. destruct pr3. reflexivity.
Defined.

Next Obligation.
  destruct a0, b. destruct pr2.
  revert e. simplify ?. simpl.
  simplify ?. simpl. reflexivity.
Defined.

Lemma concat_A1p_lemma {A} (f : A -> A) (p : forall x, f x = x) {x y : A} (q : x = y) :
  (concat_A1p p q) = (concat_A1p p q).
Proof.
  funelim (concat_A1p p q). simpl in *.
  simpl in *.
  elim Heq0 using Id_rect_dep_r. simpl. reflexivity.
  (* Fail dependent rewrite Heq0. (* bug *) *)
  (* elim Heq using Id_rect_dep_r. simpl. reflexivity. *)
Qed.

Equations ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q) :=
ap_pp _ id_refl id_refl => id_refl.

Equations concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ eq_sym q = p :=
concat_pp_V id_refl id_refl => id_refl.

Equations ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (eq_sym p) = eq_sym (ap f p) :=
ap_V f id_refl => id_refl.  

Hint Rewrite @ap_pp @ap_V : ap.
Hint Rewrite  @concat_pp_V : concat.

Equations concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) = q @ (p y) :=
concat_pA1 p id_refl := concat_p1 (p _).

Equations concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (eq_sym p @ q) = q :=
concat_p_Vp id_refl id_refl := id_refl.

Equations concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ eq_sym q) @ q = p :=
concat_pV_p id_refl id_refl := id_refl.
Hint Rewrite @concat_pA1 @concat_p_Vp @concat_pV_p : concat.
Transparent concat.
Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  : (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  now rewrite !concat_p1.
  (* now simp concat. *)
Defined.

Equations ap_p {A B : Type} (f : A -> B) {x y : A} (p q: x = y) (e : p = q) :
  ap f p = ap f q :=
ap_p f p _ id_refl := id_refl.

Instance ap_morphism (A : Type) (B : Type) x y f :
  Proper (@Id (@Id A x y) ==> @Id (@Id B (f x) (f y))) (@ap A B f x y).
Proof. reduce. now apply ap_p. Defined.

Instance reflexive_proper_proxy :
  ∀ (A : Type) (R : crelation A), Reflexive R → ∀ x : A, ProperProxy R x.
Proof. intros. reduce. apply X. Defined.

Instance isequiv_inverse A B (f:A -> B) (H:IsEquiv f) : IsEquiv (f^^-1) | 1000.
Proof.
  refine (BuildIsEquiv (@eissect _ _ f _) (@eisretr _ _ f _) _).
  intros b. 
  rewrite <- (concat_1p (eissect _ _)).
  rewrite <- (concat_Vp  (ap f^^-1 (eisretr _ (f (f^^-1 b))))).
  rewrite (whiskerR (inverse2 (ap02 f^^-1 (eisadj _ (f^^-1 b)))) _).
  refine (whiskerL _ (eq_sym (concat_1p (eissect _ _))) @ _).
  rewrite <- (concat_Vp (eissect _ (f^^-1 (f (f^^-1 b))))).
  rewrite <- (whiskerL _ (concat_1p (eissect _ (f^^-1 (f (f^^-1 b)))))).
  rewrite <- (concat_pV (ap f^^-1 (eisretr _ (f (f^^-1 b))))).
  apply moveL_M1.
  repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
  rewrite <- (concat_pp_A1 (fun a => eq_sym (eissect _ a)) _ _).
  rewrite (ap_compose f f^^-1).
  rewrite <- (ap_p_pp _ _ (ap f (ap f^^-1 (eisretr _ (f (f^^-1 b))))) _).
  rewrite <- (ap_compose f^^-1 f).
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite ap_pp, concat_p_pp.
  rewrite (concat_pp_V _ (ap f^^-1 (eisretr _ (f (f^^-1 b))))).
  repeat rewrite <- ap_V. rewrite <- ap_pp.
  rewrite <- (concat_pA1 (fun y => eq_sym (eissect _ y)) _).
  rewrite ap_compose, <- (ap_compose f^^-1 f).
  rewrite <- ap_p_pp.
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite concat_p_Vp.
  rewrite <- ap_compose.
  rewrite (concat_pA1_p (@eissect _ _ f _) _).
  rewrite concat_pV_p; apply concat_Vp.
Defined.

Definition path_contr {A} {H:Contr A} (x y : A) : x = y
  := concat (eq_sym (@contr _ H x)) (@contr _ H y).

Definition transport_inv A {P : A -> Type} (x y :A) (e : x = y) (u:P x) v:
  u = eq_sym e # v -> e # u = v.
  destruct e. exact id. 
Defined. 

Definition contr_sigma A {P : A -> Type}
  {H : Contr A} `{H0 : forall a, Contr (P a)}
  : Contr (sigma A P).
Proof.
  exists &(center A & center (P (center A))).
  intros [a Ha]. unshelve refine (path_sigma _ _ _ _ _).
  simpl. apply H. simpl. apply transport_inv.
  apply (H0 (center A)).
Defined.

Equations path_sigma_uncurried {A : Type} {P : A -> Type} (u v : sigma A P)
  (pq : sigma _ (fun p => p # u.2 = v.2))
  : u = v :=
path_sigma_uncurried &(u1 & u2) &(_ & _) &(1 & 1) := 1.
Transparent path_sigma_uncurried.

Definition pr1_path {A} `{P : A -> Type} {u v : sigma A P} (p : u = v)
: u.1 = v.1
  := ap (@pr1 _ _) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path {A} `{P : A -> Type} {u v : sigma A P} (p : u = v)
: p..1 # u.2 = v.2.
  destruct p. apply id_refl.
Defined.

Notation "p ..2" := (pr2_path p) (at level 3).

Definition eta_path_sigma_uncurried {A} `{P : A -> Type} {u v : sigma A P}
           (p : u = v) : path_sigma_uncurried _ _ &(p..1& p..2) = p.
  destruct p. apply id_refl.
Defined.

Definition eta_path_sigma A `{P : A -> Type} {u v : sigma A P} (p : u = v)
: path_sigma _ _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition path_sigma_equiv {A : Type} (P : A -> Type) (u v : sigma A P):
  IsEquiv (path_sigma_uncurried u v).
  unshelve refine (BuildIsEquiv _ _ _).
  - exact (fun r => &(r..1 & r..2)).
  - intro. apply eta_path_sigma_uncurried.
  - destruct u, v; intros [p q]; simpl in *.
    destruct p. simpl in *. destruct q.
    reflexivity.
  - destruct u, v; intros [p q]; simpl in *;
    destruct p. simpl in *. destruct q; simpl in *.
    apply id_refl.
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct r.
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  Proof.
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V.
    rewrite <- concat_p_pp.
    rewrite <- concat_p_pp.
    apply moveL_Vp. rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := @BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := @BuildEquiv A B f isequiv_adjointify.

End Adjointify.

Arguments isequiv_adjointify {A B}%type_scope (f g)%function_scope isretr issect.
Arguments equiv_adjointify {A B}%type_scope (f g)%function_scope isretr issect.

Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'
:= match h, h' with id_refl, id_refl => 1 end.

Reserved Notation "p @@ q" (at level 20).
Notation "p @@ q" := (concat2 p q)%equations : equations_scope.

(** If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. *)
Global Instance isequiv_ap {A B} f `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y) | 1000
  := isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).

Instance contr_unit : Contr unit | 0 := let x := {|
  center := tt;
  contr := fun t : unit => match t with tt => id_refl end
|} in x.


Definition path2_contr {A} {H:Contr A} {x y : A} (p q : x = y) : p = q.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r; symmetry; now apply concat_Vp.
  apply (transitivity (y:=path_contr x y)).
  - apply K.
  - symmetry; apply K.
Defined.

Instance contr_paths_contr A {H:Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := concat (eq_sym (contr x)) (contr y);
  contr := path2_contr (concat (eq_sym (contr x)) (contr y))
|} in c.

Program Instance contr_prod A B {CA : Contr A} {CB : Contr B} : Contr (prod A B).
Next Obligation. exact (@center _ CA, @center _ CB). Defined.
Next Obligation. apply path_prod; apply contr. Defined.

Definition hfiber {A B : Type} (f : A -> B) (y : B) := &{ x : A & f x = y }.

Global Arguments hfiber {A B}%type_scope f%function_scope y.
