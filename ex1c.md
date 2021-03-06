---
layout: default
title: "第1回 解説"
---

## 第1回の解説

### 課題0

Coqのインストールと利用の入門です。

### 課題1

非常に簡単な定理の証明です。

introsを行うと、ゴールの表示が次のようになります。

```
1 subgoals
P : Prop
Q : Prop
H : P
H0 : P -> Q
______________________________________(1/1)
Q
```

ここで、次の4行は「持ち物」を表します。

```
P : Prop
Q : Prop
H : P
H0 : P -> Q
```

しかし、最初の2つの「持ち物」と、次の2つの「持ち物」は別の意味です。

- P, Q は **命題** である。 (コロンの次が Prop になっている)
- H は P が正しいことの **証拠**(あるいは、**証明**) である。 (コロンの次が P になっている)
- H0 は (P -> Q) が正しいことの **証拠** である。

これらは、Coqの理論としては同一視されます。P, Q, H, H0 はそれぞれ Prop, P, (P -> Q) という**型**をもつ**変数**なのです。

簡単な型システムをもつプログラミング言語では、値とその型の関係はフラットです。しかし、Coqではこのように、Pがコロンの左側に来たり、右側に来たりします。値と型の関係は、「これは型」「これは値」という絶対的な位置関係ではなくて、「Aの型はB, Bの型はC」というような相対的な関係であるということに注意しましょう。(練習していくうちにわかると思います。)

### 課題2

仮定の持ち方が先ほどと違ったことに気づいたでしょうか。

```coq
Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
```

これを抜き出すと、次のようになります。
```coq
A -> B -> C
A /\ B -> C
```

課題1では、二つの仮定の間には -> がありました。しかし、課題2では、二つの仮定の間は /\\ で結んでいます。

正しく括弧をつけると、次のようになります。
```coq
A -> (B -> C)
(A /\ B) -> C
```

これらは、同じ意味になります。これをカリー化(currying)といいます。普通は、前者を使ったほうが使いやすいです。

### 課題3

P \\/ Q を分解すると、「Pの場合」と「Qの場合」の2つの場合分けになります。


次の定理を証明せよ。ただし、全自動で証明できてしまうautoやtautoなどのコマンドは使わないこと。

```coq
2 subgoal
P : Prop
Q : Prop
H : P
H0 : ~ P
______________________________________(1/2)
Q
______________________________________(2/2)
Q
```

これは、次の表示が省略されたものです。

```coq
2 subgoal
P : Prop
Q : Prop
H : P
H0 : ~ P
______________________________________(1/2)
Q

P : Prop
Q : Prop
H : Q
H0 : ~ P
______________________________________(2/2)
Q
```

このように、二つの場合分けができた場合は、その「持ち物」も異なることがありますが、なぜか省略されてしまうのでわかりにくいかもしれません。

また、場合分けが発生するので、(通常のプログラミング言語における条件分岐文でそうするように)インデントを行ったほうが読みやすくなります。

```coq
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros P Q H HnP.
  destruct H as [HP | HQ].
    (* Pの場合 *)
    destruct HnP.
    exact HP.

    (* Qの場合 *)
    exact HQ.
Qed.
```

さらに、Coq 8.4から使えるようになったbullet機能を使うと、見やすくなるだけではなくて保守性が上がります。

```coq
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros P Q H HnP.
  destruct H as [HP | HQ].
  - (* Pの場合 *)
    destruct HnP.
    exact HP.
  - (* Qの場合 *)
    exact HQ.
Qed.
```

### 課題4

ド・モルガンの定理です。もう1つのド・モルガンの定理は証明できません。これはCoqの論理がデフォルトでは**直観主義論理**だからです。

### 課題5

Coqのデフォルトの論理は直観主義論理なので、**排中律**は証明できません。

しかし、古典論理はある種の[二重否定変換](http://en.wikipedia.org/wiki/Double-negation_translation)によって直観主義論理に埋め込むことができます。

述語論理に対する変換は少々複雑で、Kuroda変換などが知られていますが、命題論理に対する変換としてはGlivenko変換がよく知られています。これは単に命題全体を二重否定するものです。

この問題は、排中律の二重否定なので、直観主義論理で証明できます。
