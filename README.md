# hs-bcopl
五十嵐淳著『プログラミング言語の基礎概念』

『判断』を型で，その『導出』を値で書く試みです．
REPLに型エラーなしにロードできれば，正しい導出であるということです．

現時点では『判断』を表す型をShowクラスのインスタンスできていません．
判断を表す式を評価したら導出木が出力されるといいのですが，それができない（残念な）システムです．
『判断』をShowクラスのインスタンスにする方法をご存知でしたら教えていただければ幸いです．

## 第1章

- Language.BCoPL.Peano -- ペアノ自然数
- Language.BCoPL.Nat -- 自然数の加算・乗算
- Language.BCoPL.CompareNat -- 自然数の比較
- Language.BCoPL.Exp -- 算術式
- Language.BCoPL.EvalNatExp -- 算術式の評価
- Language.BCoPL.ReduceNatExp -- 算術式の評価

## 第2章

- Language.BCoPL.MetaTheory.Nat -- 自然数の加算・乗算に関するメタ定理
- Language.BCoPL.MetaTheory.CompareNat -- 自然数の比較に関するメタ定理

