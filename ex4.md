---
layout: default
title: "第4回"
---

## 第4回の課題リスト

### 課題16 (種別:A / 締め切り : 2014/05/04)

次の定理を証明せよ。ただし、証明モードは用いないこと。

```coq

Definition tautology : forall P : Prop, P -> P
  := (* ここに証明項を書く *) .

Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := (* ここに証明項を書く *) .

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := (* ここに証明項を書く *) .

Definition tautology_on_Set : forall A : Set, A -> A
  := (* ここに証明項を書く *) .

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := (* ここに証明項を書く *) .

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := (* ここに証明項を書く *) .
```

**ヒント**

- 対話的証明モードの途中で証明項を表示するには、 Show Proof. を実行します。
- 対話的証明モードが終わったあとに証明項を表示するには、その名前を指定して Print を実行します。
  - 上の問題について、対話的証明モードで証明したものをPrintして参考にしても構いません。ただし、対話的証明モードが生成する証明項は冗長かもしれません。
- on\_Set がついているほうには、乗算や加算が出てきます。これは直積や直和に相当する概念です。また、Empty\_setは名前の通り空集合です。これらは命題バージョンと対応しているということから、Curry-Howard対応の気持ちを汲み取ってもらえればよいです。


### 課題17 (種別:A / 締め切り : 2014/05/04)

次の証明の各ステップをそれぞれrefineタクティックで置き換えよ。

```coq
Theorem hoge : forall P Q R : Prop, P \/ ~(Q \/ R) -> (P \/ ~Q) /\ (P \/ ~R).
Proof.
  (* 例 : 最初の1行は refine (fun P Q R => _). に置き換えられる *)
  intros P Q R.
  intros H.
  destruct H as [HP | HnQR].
  - split.
    + left.
      exact HP.
    + left.
      exact HP.
  - split.
    + right.
      intros HQ.
      apply HnQR.
      left.
      exact HQ.
    + right.
      intros HR.
      apply HnQR.
      right.
      exact HR.
Qed.
```


**ヒント**

- 対話証明モードのお仕事体験です。
- ひたすらShow Proofを叩いて前後での変化を見比べましょう。
- Coq 8.3以前のバージョンを使っている場合 : 8.3以前ではbulletがサポートされていないので、マイナスやプラスは取り去ってしまって構いません。

### 課題18 (種別:A / 締め切り : 2014/05/04)

次のような型 Nat を定義する。 (Church encoding)

```coq
Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).
```

Natの足し算を定義し、それが正しいことを証明せよ。ただし、NatPlusの定義には標準ライブラリの内容は使ってはいけない。

```coq
Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus(n m : Nat) : Nat :=
  (* ここに定義を書く *) .

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S O.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- Natの各要素は、fとxが与えられたとき、xにfを何回か適用して返す関数であると考えられます。この適用回数で自然数を表そうというのがこの考え方です。

### 課題19 (種別:B / 締め切り : 2014/05/11)

帰納型を使わずにイコールを定義し、それが標準ライブラリのeqの定義と同値であることを証明せよ。

```coq
Parameter A : Set.
Definition Eq : A -> A -> Prop :=
  (* ここに定義を書く *) .

Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

natの定義はおよそ次のようなものでした。 (SとOの順序など、意図的に改変している部分があります)

```coq
Inductive nat : Type :=
  | S : nat -> nat
  | O : nat.
```

一方、Natの定義は次のようなものでした。(意味深なインデント)

```coq
Definition Nat := forall A : Type,
       (A   -> A  ) ->
        A           ->
  A.
```

では、eqをChurch Encodingするとどうなるでしょうか…？

ちなみにeq Aの定義は次のようなものでした。

```coq
Inductive eq(a : A) : A -> Type :=
  eq_refl : eq a.
```

### 課題20 (種別:C / 締め切り : 2014/05/18)

次の定理を証明せよ。

```coq
Theorem nat_natbool_diff: nat <> (nat->bool).
Proof.
  (* ここに証明を書く *)
Qed.
```

