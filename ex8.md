---
layout: default
title: "第8回"
---

## 第8回の課題リスト

### 課題36 (種別:A / 締め切り : 2014/06/01)

Zの単項イデアルをZの部分集合として定義し、その中での加算とスカラー倍を定義する。下の証明の空欄を埋めよ。ring等を使ってもよい。

```
Require Import ZArith.

Section Principal_Ideal.
  Variable a : Z.

  Definition pi : Set := { x : Z | ( a | x )%Z }.

  Program Definition plus(a b : pi) : pi := (a + b)%Z.
  Next Obligation.
    (* ここを埋める *)
  Qed.

  Program Definition mult(a : Z) (b : pi) : pi := (a * b)%Z.
  Next Obligation.
    (* ここを埋める *)
  Qed.
End Principal_Ideal.
```

**ヒント**

- Program Definition は、Definitionと比べて、いくつかの部分を自動で埋めてくれます。
  1. { x : A | ... } から A への自動変換などを行えます。
  2. 証明が必要な部分を開けておくと、自動で証明を試みてくれます。
  3. 自動で証明できなかったものは、Obligationコマンドであとから手動で証明できます。
- もっぱら3の目的で使用することが多いと思われます。


### 課題37 (種別:A / 締め切り : 2014/06/01)

自然数の対の商集合として整数を定義する。下の証明の空欄を埋めよ。omega等を使ってもよい。

```
Require Import SetoidClass.

Record int := {
  Ifst : nat;
  Isnd : nat
}.

Program Instance ISetoid : Setoid int := {|
  equiv x y := Ifst x + Isnd y = Ifst y + Isnd x
|}.
Next Obligation.
Proof.
  (* ここを埋める *)
Qed.

Definition zero : int := {|
  Ifst := 0;
  Isnd := 0
|}.

Definition int_minus(x y : int) : int := {|
  Ifst := Ifst x + Isnd y;
  Isnd := Isnd x + Ifst y
|}.

Lemma int_sub_diag : forall x, int_minus x x == zero.
Proof.
  (* ここを埋める *)
Qed.

(* まず、int_minus_compatを証明せずに、下の2つの証明を実行して、どちらも失敗することを確認せよ。*)
(* 次に、int_minus_compatを証明し、下の2つの証明を実行せよ。 *)
(*
Instance int_minus_compat : Proper (equiv ==> equiv ==> equiv) int_minus.
Proof.
  (* ここを埋める *)
Qed.
*)

Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  rewrite int_sub_diag.
  reflexivity.
Qed.

Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  setoid_rewrite int_sub_diag.
  reflexivity.
Qed.
```

おまけ : ISetoidの定義においてProgram InstanceをInstanceに変更し、Next Obligation. を取り除いてもISetoidは定義できるが、続きがうまくいかなくなる。これは何故か？

**ヒント**

- 通常のイコール (Coq.Init.Logic.eq) 以外の同値関係を入れたい場合、Setoidを使います。
- Setoidによる書き換えは、通常rewriteで行えます。明示的にSetoidを使う場合は、setoid\_rewriteを使います。
- Setoidによってreplaceを行いたい場合はsetoid\_replaceを使えます。
- 通常のイコールと違い、Setoidの同値関係を保存しない写像が存在する可能性があります。例えば、この問題におけるIfst関数はSetoidの同値関係を保存しません。Setoidによる書き換えを行うためには、それぞれの関数が同値関係を保存することを逐一証明する必要があります。
- Recordは単一のコンストラクタを持ち再帰的でない型を定義するのに使えるコマンドです。メンバを取り出す関数(この例ではIfst, Isnd)が自動的に定義されることや、{| ... |} という構文でRecord型の値を記述できるという利点があります。


### 課題38 (種別:A / 締め切り : 2014/06/01)

モノイドを型クラスとして定義する。以下の空欄を埋めよ。

```
(* モノイド *)
Class Monoid(T:Type) := {
  mult : T -> T -> T
    where "x * y" := (mult x y);
  one : T
    where "1" := one;
  mult_assoc x y z : x * (y * z) = (x * y) * z;
  mult_1_l x : 1 * x = x;
  mult_1_r x : x * 1 = x
}.

Delimit Scope monoid_scope with monoid.
Local Open Scope monoid_scope.

Notation "x * y" := (mult x y) : monoid_scope.
Notation "1" := one : monoid_scope.

(* モノイドのリストの積。DefinitionをFixpointに変更するなどはOK *)
Definition product_of{T:Type} {M:Monoid T} : list T -> T := (* ここを埋める *)

Require Import Arith.

(* 自然数の最大値関数に関するモノイド。
 * InstanceをProgram Instanceにしてもよい *)
Instance MaxMonoid : Monoid nat := (* ここを埋める *) .

Require Import List.

Eval compute in product_of (3 :: 2 :: 6 :: 4 :: nil). (* => 6 *)
Eval compute in product_of (@nil nat). (* => 0 *)
```

**ヒント**

- Classの実体はRecordです。Classとして宣言すると、型クラスのように自動でインスタンスを探しに行くようになり、インスタンスを明示する必要がなくなります。
- SetoidやProperもクラスです。


### 課題39 (種別:B / 締め切り : 2014/06/08)

モナドを定義する。以下の空欄を埋めよ。

```
(* bindの記法を予約 *)
Reserved Notation "x >>= y" (at level 110, left associativity).

(* モナド *)
Class Monad(M:Type -> Type) := {
  bind {A B} : M A -> (A -> M B) -> M B
    where "x >>= f" := (bind x f);
  ret {A} : A -> M A;
  (* モナド則をここに書く *)
}.

Notation "x >>= f" := (@bind _ _ _ _ x f).

Require Import List.

Program Instance ListMonad : Monad list := {|
  bind A B m f := (* ここを埋める *);
  ret A x := (* ここを埋める *)
|}.
Next Obligation.
  (* ここに証明を書く *)
Qed.
(* 以下、ListMonadが定義できるまでNext Obligation -> Qed を繰り返す *)

(* モナドの使用例 *)

Definition foo : list nat := 1 :: 2 :: 3 :: nil.

(* 内包記法もどき *)
(*
  do x <- foo
     y <- foo
     (x, y)
*)
Definition bar := Eval lazy in
  foo >>= (fun x =>
  foo >>= (fun y =>
  ret (x, y))).

Print bar.
```

### 課題40 (種別:C / 締め切り : 2014/06/15)

Setoidを考慮したモノイドを定義せよ。その後、2つのモノイドの[(圏論的)直和](http://ja.wikipedia.org/wiki/%E7%9B%B4%E5%92%8C)を定義し、その普遍性を証明せよ。

次のテンプレートを使うとよい。 意味が変わらない範囲で適宜定義を変更してもよい。

```
Require Import SetoidClass.

(* モノイド *)
Class Monoid(T:Type) := {
  monoid_setoid : Setoid T;
  mult : T -> T -> T
    where "x * y" := (mult x y);
  mult_proper : Proper (equiv ==> equiv ==> equiv) mult;
  one : T
    where "1" := one;
  mult_assoc x y z : x * (y * z) == (x * y) * z;
  mult_1_l x : 1 * x == x;
  mult_1_r x : x * 1 == x
}.

Existing Instance monoid_setoid.
Existing Instance mult_proper.

Delimit Scope monoid_scope with monoid.
Local Open Scope monoid_scope.

Notation "x * y" := (mult x y) : monoid_scope.
Notation "1" := one : monoid_scope.

(* モノイド準同型 *)
Class MonoidHomomorphism{A B:Type}
  {monoid_A : Monoid A} {monoid_B : Monoid B}
  (f : A -> B) : Prop := {
  monoid_homomorphism_proper : Proper (equiv ==> equiv) f;
  monoid_homomorphism_preserves_mult x y:
    f (x * y) == f x * f y;
  monoid_homomorphism_preserves_one:
    f 1 == 1
}.

Existing Instance monoid_homomorphism_proper.

(* モノイドの直和 *)
Section MonoidCoproduct.
  (* A, B : モノイド *)
  Variable A B : Type.
  Context {monoid_A : Monoid A} {monoid_B : Monoid B}.

  (* AとBのモノイド直和の台集合 *)
  Definition MonoidCoproduct : Type := (* ここを埋める *) .

  (* モノイド直和の二項演算 *)
  Definitio MCmult : MonoidCoproduct -> MonoidCoproduct -> MonoidCoproduct
    := (* ここを埋める *) .

  (* MonoidCoproductの同値関係 *)
  Definition MonoidEqual : MonoidCoproduct -> MonoidCoproduct -> Prop
    := (* ここを埋める *) .

  (* 以上がモノイドになっていること *)
  Program Instance MonoidCoproductMonoid : Monoid MonoidCoproduct := {|
    monoid_setoid := {|
      equiv := MonoidEqual
    |};
    mult := MCmult;
    one := MC1
  |}.
  Next Obligation.
    (* ここを埋める *)
  Qed.
  (* ... *)

  (* A, Bから直和への標準的な埋め込み射 *)
  Definition emb_l : A -> MonoidCoproduct
    := (* ここを埋める *) .
  Definition emb_r : B -> MonoidCoproduct
    := (* ここを埋める *) .

  (* emb_lがモノイド準同型であること *)
  Instance emb_l_homomorphism : MonoidHomomorphism emb_l.
  Proof.
    (* ここを埋める *)
  Qed.

  (* emb_rがモノイド準同型であること *)
  Instance emb_r_homomorphism : MonoidHomomorphism emb_r.
  Proof.
    (* ここを埋める *)
  Qed.

  (* 普遍性 *)
  (* Universal Mapping Property *)
  Section UMP.
    (* X : モノイド *)
    Variable X : Type.
    Context {monoid_X : Monoid X}.
    (* f, g : モノイド準同型 *)
    Variable f : A -> X.
    Variable g : B -> X.
    Context {homomorphism_f : MonoidHomomorphism f}.
    Context {homomorphism_g : MonoidHomomorphism g}.

    (* 図式を可換にする射の存在 *)
    Section Existence.
      (* 図式を可換にする射 *)
      Definition h : MonoidCoproduct -> X := (* ここを埋める *) .

      (* hがモノイド準同型であること *)
      Instance homomorphism_h : MonoidHomomorphism h.
      Proof.
        (* ここを埋める *)
      Qed.

      (* hの可換性1 *)
      Lemma h_commute_l : forall a, h (emb_l a) == f a.
      Proof.
        (* ここを埋める *)
      Qed.

      (* hの可換性2 *)
      Lemma h_commute_r : forall a, h (emb_r a) == g a.
      Proof.
        (* ここを埋める *)
      Qed.
    End Existence.

    (* 図式を可換にする射の一意性 *)
    Section Uniqueness.
      (* h' : モノイド準同型 *)
      Variable h' : MonoidCoproduct -> X.
      Context {homomorphism_h' : MonoidHomomorphism h'}.

      (* h' は上のhと同じ可換性をもつ *)
      Hypothesis h'_commute_l : forall a, h' (emb_l a) == f a.
      Hypothesis h'_commute_r : forall b, h' (emb_r b) == g b.

      (* このようなh'は結局hと同一である *)
      Lemma uniqueness : forall c, h' c == h c.
      Proof.
        (* ここを埋める *)
      Qed.
    End Uniqueness.
  End UMP.
End MonoidCoproduct.
```
