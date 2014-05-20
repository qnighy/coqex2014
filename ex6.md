---
layout: default
title: "第6回"
---

## 第6回の課題リスト

### 課題26 (種別:A / 締め切り : 2014/05/18)

次の定理を証明せよ。

なお、auto, tauto, omega, ring, field, lia, psatz, nia などの自動証明タクティックを用いてもよい。

```coq
Goal (221 * 293 * 389 * 397 + 17 = 14 * 119 * 127 * 151 * 313)%nat.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- Coqで計算を進めるコマンドには、simpl, lazy, cbv, compute, vm\_computeなどがあります。
- 自然数Nをあらわすnatのオブジェクトは、コンストラクタSをN回使っています。上の式を展開するとどれくらいのサイズになるでしょうか。
- [標準ライブラリ](http://coq.inria.fr/stdlib/)を探してみましょう。

### 課題27 (種別:A / 締め切り : 2014/05/18)

次の定理を証明せよ。

なお、auto, tauto, omega, ring, field, lia, psatz, nia などの自動証明タクティックを用いてもよい。

```coq
Require Import ZArith.

Lemma hoge : forall z : Z, (z ^ 4 - 4 * z ^ 2 + 4 > 0)%Z.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- 非負であることは、平方完成によって証明できます。
- ゼロにならないことを示すには、zの二乗が2にならないことを示す必要があります。これはどうしたらよいでしょうか。
- 線形の不等式のような形をしている命題は、omegaで証明するのがよいでしょう。(例, zは0, 1, 2以上または-1以下のいずれかである、などの命題。)
- 多項式の変形はreplace A with B by ringなど、ringタクティックを用いて証明するのがよいでしょう。ringの派生としてring\_simplifyもあります。

### 課題28 (種別:B / 締め切り : 2014/05/25)

次の定理を証明せよ。(出典 : [anarchy proof](http://web.archive.org/web/20101125111131/http://as305.dyndns.org/aps/problem/view/29))

なお、auto, tauto, omega, ring, field, lia, psatz, nia, fourier などの自動証明タクティックを用いてもよい。

```
Require Import Reals.

Theorem PI_RGT_3_05 : (PI > 3 + 5/100)%R.
Proof.
  (* ここに証明を書く *)
Qed.
```

**ヒント**

- 実数の線形不等式はfourierで示せることが多いです。
- 割り算を含む式の変形はfieldタクティックを使うと便利かもしれません。使い方はringと同じです。fieldの派生としてfield\_simplifyもあります。
- PIに関する不等式は[Ratan](http://coq.inria.fr/stdlib/Coq.Reals.Ratan.html)の最後の方にあります。これはπの有名な級数による近似です。

### 課題29 (種別:C / 締め切り : 2014/06/01)

次の定理を証明せよ。

なお、auto, tauto, omega, ring, field, lia, psatz, nia などの自動証明タクティックを用いてもよい。

```
Require Import ZArith.

Definition prime1(z : Z) : Prop :=
  z <> 0%Z /\
  forall a b, ((z | a * b) -> (z | a) \/ (z | b))%Z.

Definition prime2(z : Z) : Prop :=
  forall a b, (z = a * b -> (a | 1) \/ (b | 1))%Z.

Lemma prime1_prime2_iff z : prime1 z <-> prime2 z.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題30 (種別:C / 締め切り : 2014/06/01)

次の定理を証明せよ。

なお、auto, tauto, omega, ring, field, lia, psatz, nia などの自動証明タクティックを用いてもよい。

```
Require Import QArith.

Lemma sqrt_2 : forall q : Q, ~(q * q == 1 + 1)%Q.
Proof.
  (* ここに証明を書く *)
Qed.
```

