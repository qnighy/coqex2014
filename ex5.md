---
layout: default
title: "第5回"
---

## 第5回の課題リスト (予定) (途中)

### 課題21 (種別:A / 締め切り : 2014/05/11)

次の定理を証明せよ。ただし、Coq.LogicおよびCoq.Setsに定義されている公理を用いても構わない。各定理について、それを証明するのに必要な公理はできるだけ弱いものに留めるのが望ましい。

なお、autoやtautoなどの自動証明タクティックを用いてもよい。

```coq
Lemma ABC_iff_iff : forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
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
