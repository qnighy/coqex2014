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

