---
layout: default
title: "第9回"
---

## 第9回の課題リスト

### 課題41 (種別:A / 締め切り : 2014/06/15)

splitを試し、成功したら生成された全てのサブゴールで再帰的にsplitを試し続けるタクティックを定義せよ。

```coq
Ltac split_all := (* ここに定義する *) .

(* 以下は動作確認用 *)

Lemma bar :
  forall P Q R S : Prop,
    R -> Q -> P -> S -> (P /\ R) /\ (S /\ Q).
Proof.
  intros P Q R S H0 H1 H2 H3.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma baz :
  forall P Q R S T : Prop,
    R -> Q -> P -> T -> S -> P /\ Q /\ R /\ S /\ T.
Proof.
  intros P Q R S T H0 H1 H2 H3 H4.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma quux :
  forall P Q : Type, P -> Q -> P * Q.
Proof.
  intros P Q H0 H1.
  split_all.
  - assumption.
  - assumption.
Qed.

Record foo := {
  x : (False -> False) /\ True /\ (False -> False);
  y : True;
  z : (False -> False) /\ True
}.

Lemma hogera : foo.
Proof.
  split_all.
  - intros H; exact H.
  - intros H; exact H.
  - intros H; exact H.
Qed.
```

**ヒント**

- マニュアルの[8章はタクティック集](http://coq.inria.fr/refman/Reference-Manual010.html)、[9章はタクティック言語の文法など](http://coq.inria.fr/refman/Reference-Manual011.html)、[10章は3つの発展的なタクティックの詳細](http://coq.inria.fr/refman/Reference-Manual012.html)です。これらが一次資料です。
- Ltac はタクティックの再帰的定義ができます。つまり、定義されたタクティックの中で自分自身を呼ぶことができます。
- try タクティカルを使いましょう。

### 課題42 (種別:A / 締め切り : 2014/06/15)

自然数におけるlog関数(底は2)を以下のテンプレートに従って定義せよ。

```coq
Require Import Arith.
Require Import Omega.
Require Import Recdef.

Function log(n:nat) {wf lt n} :=
  if le_lt_dec n 1 then
    0
  else
    S (log (Div2.div2 n)).
Proof.
  (* ここを埋める *)
Qed.

```

**ヒント**

- Fixpointでは構造に基づく帰納法しか書けませんでした。Coqが自動的に停止性を判断できないような関数の定義をするために、Functionコマンドが用意されています。停止性はwf (パラメーターのうちの1つが整礎的な関係に従って降下していくことを示す) または measure (パラメーターのうちの1つに自然数の重みを定める関数があり、再帰呼び出しはこの重みが減る方向に進むということを示す) の2つの方法があります。

### 課題43 (種別:B / 締め切り : 2014/06/22)

ゴールがandの連なった形であるとき、これをandの形になっている限りsplitし続けるタクティックを定義せよ。課題41と違い、and以外の形の場合はsplitしてはいけない。

```coq
Ltac split_all := (* ここに定義する *) .

(* 以下は動作確認用 *)

Lemma bar :
  forall P Q R S : Prop,
    R -> Q -> P -> S -> (P /\ R) /\ (S /\ Q).
Proof.
  intros P Q R S H0 H1 H2 H3.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma baz :
  forall P Q R S T : Prop,
    R -> Q -> P -> T -> S -> P /\ Q /\ R /\ S /\ T.
Proof.
  intros P Q R S T H0 H1 H2 H3 H4.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma quux :
  forall P Q : Type, P -> Q -> P * Q.
Proof.
  intros P Q H0 H1.
  split_all.
  split.
  - assumption.
  - assumption.
Qed.
```

**ヒント**

- match goal with ... end 構文を使いましょう。この構文の使い方についてはマニュアルの9章の文法定義を追うのがよいかと思います。

### 課題44 (種別:C / 締め切り : 2014/06/29)

課題42で証明したlog関数に関する性質を証明せよ。

```coq
Require Import Arith.
Require Import Omega.
Require Import Recdef.

Function log(n:nat) {wf lt n} :=
  if le_lt_dec n 1 then
    0
  else
    S (log (Div2.div2 n)).
Proof.
  (* ここを埋める *)
Qed.
(* ここまでは課題42 *)

Fixpoint pow(n:nat) :=
  match n with
  | O => 1
  | S n' => 2 * pow n'
  end.

Lemma log_pow_lb: forall n, 1 <= n -> pow (log n) <= n.
Proof.
  intros n H.
  functional induction (log n).
  (* ここを埋める *)
Qed.

```

**ヒント**

- functional inductionタクティックを使うと、Functionで定義した計算の構造に従う帰納法を行うことができます。


### 課題45 (種別:C / 締め切り : 2014/06/29)

次の定理を証明せよ。なおLtacを使わない手法も考えられ、それを使っても良い。

証明の方法によっては処理に時間がかかることに注意すること。(例えば、30秒程度かかったりする。)

(出典: [anarchy proof: Collatz conjecture](http://web.archive.org/web/20101125111101/http://as305.dyndns.org/aps/problem/view/20))

```coq
Require Import ZArith.
Local Open Scope Z_scope.

Inductive Collatz: Z -> Prop :=
| CollatzOne: Collatz 1
| CollatzEven: forall x, Collatz x -> Collatz (2*x)
| CollatzOdd: forall x, Collatz (3*x+2) -> Collatz (2*x+1).

Theorem Collatz_1000: forall x, 1 <= x <= 1000 -> Collatz x.
Proof.
  (* ここを埋める *)
Qed.
```
