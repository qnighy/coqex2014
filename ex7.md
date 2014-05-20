---
layout: default
title: "第7回"
---

## 第7回の課題リスト

課題αは提出は不要ですが、証明を複数ファイルに分割する方法なので重要です。ぜひとも出来るようにしておきましょう。

ただし、出題の都合上、課題αの内容は他の問題を解くのには必要ないと思われます。

### 課題α (種別:A / 締め切り : 2014/05/25)

二つ以上のファイルからなる証明を用意し、コンパイルせよ。coq\_makefileを使わない方法と使う方法がある。どちらか一方でもよいが、両方試すとよい。

例えば、次のような二つの証明を用意する。

Ternary.v

```
Delimit Scope tern_scope with tern.

Inductive tern := true | intermed | false.

Definition andt a b :=
  match a, b with
  | false, _ | _, false => false
  | intermed, _ | _, intermed => intermed
  | _, _ => true
  end.

Notation "a && b" := (andt a b) : tern_scope.
```

TernaryProperties.v

```
Require Import Ternary.

Lemma andt_assoc a b c : (a && (b && c) = (a && b) && c)%tern.
Proof.
  destruct a; destruct b; destruct c; reflexivity.
Qed.
```

コンパイルに成功したら、CoqIDEでこれらを編集できるか試してみよ。

例1) Ternary.vをコンパイルした上で、TernaryProperties.vをCoqIDE上で開き、最後まで証明が通ることを確認する。TernaryProperties.vを書き換えて、andtが可換であることの証明を書き加える。

例2) 例1に続いて、Ternary.vの内容を書き換えて、論理和演算を定義してみる。これをコンパイルし、TernaryProperties.vを開いているCoqIDE側でその内容をリロードする。その後、TernaryProperties.vに論理和演算に関する証明を書き加える。

この課題は提出不要だが、提出しても構わない。

**ヒント**

- この課題を行うためには、Coqをコマンドラインから呼び出す必要があります。そのために、Coqのバイナリのあるディレクトリにパスを通す必要があります。
  - パスの設定方法はいくつかあります。「[path 設定](https://www.google.co.jp/search?q=path+%E8%A8%AD%E5%AE%9A&ie=UTF-8)」などで検索するといいでしょう。また、Windowsの場合は、[Rapid Environment Editor](http://www.rapidee.com/) ([窓の杜での説明](http://www.forest.impress.co.jp/library/software/rapidee/)) を用いるのがオススメです。
  - コマンド・プロンプトの使い方はここでは説明しません。
- Coqコードのコンパイルには、coqcコマンドを使います。
  - coqc [オプション] ファイル名
  - オプション -R path/to/dir Path.To.CoqModule : ディレクトリ path/to/dir をCoqのモジュールシステムにおけるPath.To.CoqModuleに再帰的に対応づけます。
  - オプション -I path/to/dir Path.To.CoqModule : ディレクトリ path/to/dir をCoqのモジュールシステムにおけるPath.To.CoqModuleに対応づけます。
  - オプション -I path/to/dir : ディレクトリ path/to/dir をCoqのモジュールシステムにおける最上位に対応づけます。
- coq\_makefileを使うと、Coqのコード用のMakefileを生成することができます。
  - -f Make : Makefileの元となるファイル(Makeという名前にすることが多い)を指定します。ここには、上記のようなオプションや、コンパイル対象となるファイル(.vファイルや.ml4ファイルなど)を改行区切りで列挙します。
  - -o Makefile : 出力先を指定します。通常はMakefileというファイル名を指定します。
- Makefileが出力されたら、次のようなことができます。
  - make : 証明をコンパイルします。
  - make clean : 証明のコンパイルによって生成されたファイルを削除し、元の状態に戻します。
- Require コマンドは、コンパイルされた証明(.voファイル)を要求します。したがって、複数ファイルからなる証明をCoqIDE上で編集するときは、それ以前の証明をコンパイルする必要があります。
- 当然ですが、Requireが依存する証明を書き換えて再コンパイルしても、CoqIDEは自動で依存先をリロードしたりはしません。したがって、証明を所定の位置まで巻き戻して、Requireを再実行する必要があります。

### 課題31 (種別:A / 締め切り : 2014/05/25)

Sectionを使って、非空なリストを表すposlistを定義する。この定義を埋めよ。

```
(* Section の練習 *)

Section Poslist.
  (* このセクションの中では、Aが共通の変数として使える。 *)
  Variable A : Type.
  (* 非空なリスト *)
  Inductive poslist : Type := (* ここを埋める *) .

  Section Fold.
    (* 二項演算 *)
    Variable g : A -> A -> A.

   (* gによって畳み込む。
    * 次のどちらかを定義すること。どちらでもよい。
    * 左畳み込み : リスト [a; b; c] に対して (a * b) * c を計算する。
    * 右畳み込み : リスト [a; b; c] に対して a * (b * c) を計算する。
    *)
    Definition fold : poslist -> A := (* ここに定義を書く *).
    (* DefinitionをFixpointなどに置き換えてもよい。 *)
  End Fold.
End Poslist.
(* Poslistから抜けたことにより、poslistは変数Aについて量化された形になる。 *)

(* このリストに関するmap関数 *)
Section PoslistMap.
  Variable A B : Type.
  Variable f : A -> B.

  Definition map : poslist A -> poslist B := (* ここに定義を書く *)
End PoslistMap.

(* 今回は証明すべきことはないので、定義を正確に *)
```

定義を埋めたあと、それぞれの定義をPrintで出力してみよ。Sectionから抜ける前と後の違いを調べてみよ。(これについて書く必要はない。)

**ヒント**

- 同じ変数や仮定を使いまわすときは、この例のようにSectionで囲うと便利です。
- Sectionから抜けると、変数として仮定されていたものがforallの形でSection内の定義に自動的に付加されます。
- Section内の変数はVariable, Variablesで宣言します。仮定は、Hypothesis, Hypothesesで宣言します。(これらの効果は同じです。意味に応じて使い分けてください。)
- Variableの亜種として、Contextというものもあります。
- Section内では、DefinitionとLetは異なる効果を持ちます。気になる人は確認してみてください。

### 課題32 (種別:A / 締め切り : 2014/05/25)

半群とは、結合的な二項演算を持つ集合のことである。

次のソースを埋めて、自然数の乗算のなす半群と、自然数の最小値関数のなす半群を定義せよ。また、半群の直積を定義せよ。

G0とG1の(半群としての)直積とは、G0とG1の(集合としての)直積を台集合とし、二項演算は単に左側をG0の二項演算、右側をG1の二項演算で計算するものを入れたものである。

```
Require Import Arith.

Module Type SemiGroup.
  Parameter G : Type.
  Parameter mult : G -> G -> G.
  Axiom mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
End SemiGroup.

Module NatMult_SemiGroup <: SemiGroup.
  (* ここを埋める *)
End NatMult_SemiGroup.

Module NatMax_SemiGroup <: SemiGroup.
  (* ここを埋める *)
End NatMax_SemiGroup.

Module SemiGroup_Product (G0 G1:SemiGroup) <: SemiGroup.
  (* ここを埋める *)
End SemiGroup_Product.

```

**ヒント**

モジュールの練習です。モジュールは、名前空間としての用途の他に、このように構造の入った型を抽象化する働きもあります。

CoqのモジュールシステムはほぼOCamlのモジュールシステムと同じものです。OCamlのモジュールシステムは有用ですが、Coqのモジュールシステムは他のCoqの機能(ClassやCanonical Structure)で代替できることが多く、OCamlのそれと比べるとやや存在感が薄いかもしれません。

なお、Module Type中で用いられているParameterやAxiomは公理扱いではありません。

### 課題33 (種別:B / 締め切り : 2014/06/01)

1. 課題32の半群モジュール型を参考にして、モノイドを表すモジュール型 Monoid を定義せよ。
2. list boolに自然なモノイドの構造を入れ、Monoid型をもつモジュールとして定義せよ。
3. モノイドの元の冪乗(指数は自然数)を定義し、指数法則を証明せよ。これを定義する際、定義済みのMonoidモジュールを直接変更するのではなく、MonoidモジュールMを引数にとる新たなモジュールを定義すること。
4. 2で定義したlist boolのモジュールと、3で定義した冪乗のモジュールを合成して、新たなモジュールを作成せよ。

**ヒント**

モジュールへの機能の追加の練習です。[標準ライブラリ](http://coq.inria.fr/stdlib/)のCoq.Structuresの記述を参考にするとよいでしょう。

### 課題34 (種別:C / 締め切り : 2014/06/08)

上記の半群の定義は、等号としてイコールを使っていた。これを改め、[Coq.Structures.Equalities](http://coq.inria.fr/stdlib/Coq.Structures.Equalities.html)のEqualityTypeを用いるように書き換えよ。このとき、演算がEqualityTypeのeqに互換であること、すなわち forall x y z w, x == y -> z == w -> x * z == y * w を条件として課す必要があることに注意すること。


### 課題35 (種別:C / 締め切り : 2014/06/08)

課題34で定義した半群について、半群Gが与えられたとき、Gの中心化半群を返すモジュールを定義せよ。Gの中心化半群とは、Gの全ての元と可換な元全体からなるGの部分半群である。
