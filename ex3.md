---
layout: default
title: "第3回"
---

## 第3回の課題リスト (予定) (途中)

### 課題11 (種別:A / 締め切り : 2014/04/27)

次の定理を証明せよ。(ringタクティックやomegaタクティックを用いても構わない。)

```coq
Require Import Arith.

Fixpoint sum_odd(n:nat) : nat :=
  match n with
  | O => O
  | S m => 1 + m + m + sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- sum\_odd は (2n - 1) 以下の奇数の和を計算する関数です。
- 帰納法を回すにはinductionタクティックを使います。
- inductionのあとにはsimplを実行することが多いです。
- S は自然数に1を足す関数です。

### 課題12 (種別:A / 締め切り : 2014/04/27)

次の定理を証明せよ。 (出典 : [anarchy proof](http://as305.dyndns.org/aps/problem/view/9))

```coq
Require Import Lists.List.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- inductionタクティックは自然数以外にも適用できます。リストに対して適用した場合、リストの**構造**に対する帰納法になります。(長さに関する帰納法にはなりません。)

### 課題13 (種別:B / 締め切り : 2014/05/04)

1. [自然数の定義](http://coq.inria.fr/stdlib/Coq.Init.Datatypes.html#nat)を参考にして、**正の整数**をあらわすデータ型を帰納的に定義せよ。
2. [自然数の足し算の定義](http://coq.inria.fr/stdlib/Coq.Init.Peano.html#plus)を参考にして、上で定義した正の整数に関する足し算を定義せよ。
3. 上で定義した足し算が結合的であることを証明せよ。

以下のテンプレートを参考にしてもよい。

```coq
(* コンストラクタの名前は例えば、SOとSにするとよい。 *)
Inductive pos : Set :=
  (* posの定義を書く *) .

Fixpoint plus(n m:pos) : pos := (* plusの定義を書く *) .

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  (* 証明を書く *)
Qed.
```

**ヒント**

足し算が左側の数に関する帰納法で定義されているとき、足し算の結合性は一番左の数に関する帰納法のみで証明できます。(中央と右の数に関する帰納法は必要ありません。)

### 課題14 (種別:C / 締め切り : 2014/05/11)

次の定理を証明せよ。

```coq
Theorem FF: ~exists f, forall n, f (f n) = S n.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題15 (種別:C / 締め切り : 2014/05/11)

次の定理を証明せよ。

```coq
Inductive Tree:Set :=
  | Node: list Tree -> Tree.

Theorem Tree_dec: forall a b:Tree, {a=b} + {a<>b}.
Proof.
  (* ここに証明を書く *)
Qed.
```

## 説明

帰納法はCoqの核となる部分ですが、ここでは基本的な練習ができる3問と発展的な2問を用意してみました。

問12以外にも、[anarchy proof](http://as305.dyndns.org/aps/problem)には帰納法に関連する練習問題がいくつかあります。帰納法がメインの問題と思われるものをいくつか抜き出してみます。

- [Induction by tree height](http://as305.dyndns.org/aps/problem/view/7)
- [Seven trees](http://as305.dyndns.org/aps/problem/view/8)
- [Ackermann](http://as305.dyndns.org/aps/problem/view/14)
- [Prop to Type](http://as305.dyndns.org/aps/problem/view/15) (難)
- [Fibonacci function](http://as305.dyndns.org/aps/problem/view/21)

