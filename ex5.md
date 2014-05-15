---
layout: default
title: "第5回"
---

## 第5回の課題リスト (予定) (途中)

下の方に説明があります。

### 課題21 (種別:A / 締め切り : 2014/05/11)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。

なお、autoやtautoなどの自動証明タクティックを用いてもよい。

```coq
(* 必要な公理を入れる *)

Lemma ABC_iff_iff :
    forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
Proof.
  (* ここに証明を書く *)
Qed.

(* 必要な公理を入れる *)

Goal
  forall P Q R : Prop,
  (IF P then Q else R) ->
  exists b : bool,
  (if b then Q else R).
Proof.
  (* ここに証明を書く *)
Qed.

(* 必要な公理を入れる *)

Goal
  forall P Q R : nat -> Prop,
  (forall n, IF P n then Q n else R n) ->
  exists f : nat -> bool,
  (forall n, if f n then Q n else R n).
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- 最初の問題は直観主義論理では証明できません。
- 最後の2問はよく似た形をしていますが……？
- IF then else の定義は[Coq.Init.Logic](http://coq.inria.fr/stdlib/Coq.Init.Logic.html)にあります。

### 課題22 (種別:A / 締め切り : 2014/05/11)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。

```
(* 必要な公理を入れる *)

Record isomorphism{A B : Type} (f : A -> B) : Prop := {
  inverse : B -> A;
  is_retraction b : f (inverse b) = b;
  is_section a : inverse (f a) = a
}.

Notation isomorphic A B :=
  (exists f, @isomorphism A B f).

Lemma neg_unique :
  forall A,
    { isomorphic (A -> Empty_set) Empty_set } +
    { isomorphic (A -> Empty_set) unit }.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- Aから空集合への写像全体からなる集合は、空集合または1点集合と同型である、という定理です。
- isomorphic の証明の仕方については、次の例を参考にしてください。

```
(* isomorphic の証明の仕方 *)
Record isomorphism{A B : Type} (f : A -> B) : Prop := {
  inverse : B -> A;
  is_retraction b : f (inverse b) = b;
  is_section a : inverse (f a) = a
}.

Notation isomorphic A B :=
  (exists f, @isomorphism A B f).

Lemma option_unit_isom : isomorphic (option unit) bool.
Proof.
  (* A -> B の写像を指定する *)
  exists (fun o => match o with Some _ => true | None => false end).
  (* その逆写像 B -> A を指定する *)
  exists (fun b : bool => if b then Some tt else None).
  - intros [|]; reflexivity.
  - intros [[]|]; reflexivity.
Qed.
```


### 課題23 (種別:B / 締め切り : 2014/05/18)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。

```
Definition compose {A B C} (f : A -> B) (g : B -> C) :=
  fun x => g (f x).

Parameter X Y : Type.
Parameter f : X -> Y.

Axiom epi : forall Z (g h : Y -> Z), compose f g = compose f h -> g = h.

(* 必要な公理を入れる *)

Lemma surj : forall y, exists x, f x = y.
Proof.
  (* ここに証明を書く *)
Qed.

(* 必要な公理を入れる *)

Lemma split_epi : exists g, compose g f = id.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- surj と split\_epi はそれぞれ、「集合におけるエピ射は全射である」ことと、「集合におけるエピ射はレトラクションである」ことを意味します。
- 参考資料 : [全射 - Wikipedia](http://ja.wikipedia.org/wiki/%E5%85%A8%E5%B0%84), [Epimorphism - Wikipedia](http://en.wikipedia.org/wiki/Epimorphism), [Surjective Functions - Wikipedia](http://en.wikipedia.org/wiki/Surjective_function), [epimorphism in nLab](http://ncatlab.org/nlab/show/epimorphism), [split epimorphism in nLab](http://ncatlab.org/nlab/show/split+epimorphism)

### 課題24 (種別:C / 締め切り : 2014/05/25)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。

```coq
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.SetoidClass.

Parameter A : Type.
Parameter SetoidA : Setoid A.
Existing Instance SetoidA.

(* 必要な公理を入れる *)

Definition Q : Type := (* 定義を書く *) .

Definition pi(a : A) : Q := (* 定義を書く *) .

Lemma pi_surj : forall x, exists a, pi a = x.
Proof.
  (* ここに証明を書く *)
Qed.

Lemma pi_ker : forall a b, pi a = pi b <-> a == b.
Proof.
  (* ここに証明を書く *)
Qed.

(* 必要な公理を入れる *)

Lemma representative_exists :
  exists f : A -> A, forall a b, f a = f b <-> a == b.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題25 (種別:C / 締め切り : 2014/05/25)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。

```coq
Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatMult(n m : Nat) : Nat :=
  fun A f => n _ (m _ f).

Lemma NatMult_comm: forall n m, NatMult n m = NatMult m n.
Proof.
  (* ここに証明を書く *)
Qed.

(* 上のかわりに、次の定理を証明してもよい *)
Lemma NatMult_not_comm: ~forall n m, NatMult n m = NatMult m n.
Proof.
  (* ここに証明を書く *)
Qed.
```

## 説明

Coqのベースとなる論理は pCIC という型理論です。

型理論自体は単なる形式的な体系であり、それにどういう意味を割り当てるかにはある程度の任意性があります。通常の Coq では、型に集合を対応させて考えます。例えば、 nat という型は自然数全体の集合のことを指していると考えます。(ただし、Prop型をもつ型には命題を対応させます。)

pCIC 自体が強力な推論体系であり、かなりの証明能力を有しますが、集合論モデル的には正しいのに pCIC だけでは証明できない命題がいくつかあります。それらについては、公理として仮定することになります。

[Coq.Logicに用意されている公理についていくつか説明を書いた](http://qnighy.hatenablog.com/entry/2014/04/22/214515)ので、参考にしてください。

今回の問題は、これらの公理のどれが必要かを考える練習です。よくわからない場合は、片っ端から公理を仮定して証明に臨んでも構いません。余裕がある人は、できるだけ少ない(弱い)公理だけで証明できるか考えてみましょう。
