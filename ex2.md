---
layout: default
title: "第2回"
---

## 第2回の課題リスト (予定) (途中)

### 課題6 (種別:A / 締め切り : 2014/04/20)

次の定理を証明せよ。ただし、全自動で証明できてしまうomegaなどのタクティックは使わないこと。

```coq
Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

この課題は、既存の定理を使用する練習です。

- CoqIDEで、Escキーを押すと、下に検索画面が出てきます。
- リストから SearchAbout を選んで(または自分で入力して)、左のテキストボックスにクエリを入力します。
- ここでは、(\_ + \_ < \_ + \_) (カッコも含む) と入力してみましょう。すると検索結果が出てきます。
- 出てきたなかから適切そうな定理を選び、applyしてみましょう。

### 課題7 (種別:A / 締め切り : 2014/04/20)

次の定理を証明せよ。

```coq
Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  (* ここに証明を書く *)
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  (* ここに証明を書く *)
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

量化を含む命題の取り扱いの練習です。

- forallがゴールにあるとき: introsを使います。
- forallの形をした仮定Hを使う
  - applyでそのまま使える場合があります。
  - apply (H x)とすると、Hをxで具体化した定理を適用できます。これはapplyに限らず、項を要求する文脈で使うことができます。
  - specializeタクティックを使うこともあります。
- existsがゴールにあるとき : 具体的にxという値が条件を満たすことを証明したいときは、exists x. を使います。
- existsの形をした仮定Hを使う : destructを使います。

### 課題8 (種別:A / 締め切り : 2014/04/20)

次の定理を証明せよ。ただし、全自動で証明できてしまうringなどのタクティックは使わないこと。

```coq
Require Import Arith.

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

等式を含む命題の取り扱いの練習です。

- 証明済みの等式は SearchAbout を使って探してみましょう。
- 等式はrewriteを使うことで利用できます。逆向きに書き換えたいときは矢印 <- を使います。
- 等式の両側が同じ形のとき、reflexivityで証明を終了できます。

### 課題9 (種別:B / 締め切り : 2014/04/27)

次の定理を証明せよ。ただし、全自動で証明できてしまうringなどのタクティックは使わないこと。

```coq
Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  (* ここに証明を書く *)
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

定義に基づいて計算が進められる箇所がある場合は、simplを試してみましょう。unfoldが有効な場合もあります。

### 課題10 (種別:C / 締め切り : 2014/05/04)

次の定理を証明せよ。

```coq
Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  (* ここに証明を書く *)
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  (* ここに証明を書く *)
Qed.
```
