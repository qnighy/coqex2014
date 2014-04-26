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
