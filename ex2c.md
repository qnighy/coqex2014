---
layout: default
title: "第2回 解説"
---

## 第2回の解説

### 課題6

定理を探して適用する練習です。例えば、plus\_lt\_compat\_rを見つけて適用できればOKです。

### 課題7

量化を含む命題の取り扱いの練習です。

ここで出てくるPやQは、「**数値**を受け取って**命題**を返す**関数**」です。前に見たように、命題は**型**ですが、それを**値**と見なして演算の対象とすることができるというわけです。このように、「型自身も値として見なせる」というのがCoqの型システムの(より単純な型システムと比べた時の)特徴の一つです。

### 課題8

rewrite を使って書き換えを行うことを想定していましたが、rewriteを使わずにapplyだけで証明した人もいました。

Coqに出てくる等式も、実はCoqの組み込みではなくて、標準ライブラリとして定義されているものです。これを直接扱うのは面倒なので、普通はrewriteなどのタクティックを用いて操作します。

### 課題9

見ればわかる等式ですが、rewriteを使って示そうとするとなかなか大変です。

実際には、このような簡単な形をした式は自動で証明できることがあります。例えば、ringタクティックは、加算や乗算でできている等式について、その正しさを自動で証明することができます。今後、このような命題を示す必要が出てきたら、そういった自動化タクティックを試してみましょう。

### 課題10

ここで出てくる G は、群です。

群の定義において、通常は単位元が両方向に単位的であり、逆元も両方向に打ち消せることを仮定しますが、これは実は片方の組だけ仮定するともう一方が出るということが知られています。それを示すのがこの問題です。
