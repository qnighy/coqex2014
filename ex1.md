---
layout: default
title: "第1回"
---

## 第1回の課題リスト (予定)

資料は下の方にあるので確認しておいてください。

### 課題0の1 (種別:A / 締め切り : 2014/04/13)

Coqをダウンロードして、実行できるようにせよ。

**ヒント**

- Windowsの場合: [Download | The Coq Proof Assistant](http://coq.inria.fr/download)の coq-installer-8.4pl3.exe をダウンロード、実行してインストーラーの指示に従ってインストールしてください。
- Mac OS Xの場合: [Download | The Coq Proof Assistant](http://coq.inria.fr/download)の coqide-8.4pl2.dmg を開き、内容物をApplicationsなどに展開してください。
- その他: Ubuntuなどではパッケージ管理システムからCoqおよびCoqIDEをインストールすることができます。そうでない場合は、ソースコードからビルドする必要があるかもしれません。

### 課題0の2 (種別:A / 締め切り : 2014/04/13)

CoqIDEを起動し、以下のコードを打ち込め。

```coq
Theorem tautology : forall P : Prop, P -> P.
Proof.
  intros P H.
  assumption.
Qed.
```

次のことを確認せよ。

- CoqIDEのツールバーにある下向きの矢印(またはメニューのNavigationからForward)をクリックして、証明の実行が先に進むことを確認せよ。
- 同様に、上向きの矢印(またはメニューのNavigationからBackward)をクリックして、証明の実行を元に戻せることを確認せよ。
- 緑色に塗られた部分は編集できないことを確認せよ。

また、同様に次のコードを打ち込め。

```coq
Theorem wrong : forall P : Prop, P.
Proof.
  intros P.
Qed.
```

これを最後まで実行しようとするとどのようになるか調べよ。

### 課題1 (種別:A / 締め切り : 2014/04/13)

次の定理を証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題2 (種別:A / 締め切り : 2014/04/13)

次の定理を証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題3 (種別:A / 締め切り : 2014/04/13)

次の定理を証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題4 (種別:B / 締め切り : 2014/04/20)

次の定理を全て証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  (* ここに証明を書く *)
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  (* ここに証明を書く *)
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  (* ここに証明を書く *)
Qed.
```

### 課題5 (種別:C / 締め切り : 2014/04/20)

次の定理を証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
  (* ここに証明を書く *)
Qed.
```

## 説明

### 証明モードの読み方

証明はProofで始まってQedで終わります。この間、CoqIDEの右上の画面は例えば次のようになっています。

```
1 subgoals
P : Prop
H : P
______________________________________(1/1)
P
```

水平線の上と下では意味が真逆なので注意してください。

- 水平線の上 : このサブゴールで**使ってよい仮定**
- 水平線の下 : このサブゴールで**証明すべき命題**

「AかつB」を証明する場合などで、複数の命題を証明する場合があります。これを**サブゴール**が複数あるといいます。このときは水平線がサブゴールの数だけ出てきます。使ってよい仮定はサブゴールによって異なりますが、一番上のサブゴールの仮定のみ表示されます。タクティックは一番上のサブゴールに対して実行されます。

記号論理学経験者向けの説明: Coqの証明は基本的に「証明図(証明木)を下から書く」という手順になります。このイメージを持っておくとわかりやすいかもしれません。

### 命題論理の証明

さて、今回は命題論理の証明です。

まず、ドキュメントとして次のページはよく使うので覚えておきましょう。

- [タクティック一覧](http://coq.inria.fr/refman/tactic-index.html)
- [標準ライブラリ](http://coq.inria.fr/stdlib/)

また、Coqの日本語資料はいくつか存在しますので、いろいろGoogle検索で頑張って調べてみてください。

今回の課題は、少なくとも以下のタクティック(証明用のコマンドのこと)を覚えていれば証明できると思います

- introsタクティック(introタクティック)
- leftタクティックとrightタクティック
- destructタクティック
- applyタクティック
- splitタクティック

そのほか、次のタクティックも覚えておくとよいでしょう。

- exactタクティック
- assumptionタクティック
- contradictタクティック
- contradictionタクティック

また、今回は禁止ですが、次の自動証明コマンドもよく使われます。

- autoタクティック
- tautoタクティックとintuitionタクティック
