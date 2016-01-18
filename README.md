# hs-bcopl 五十嵐淳著『プログラミング言語の基礎概念』

## データレベルプログラム

自動導出システムを実装しようという試み

### 第1章

- ``Language.BCoPL.DataLevel.Peano``： ペアノ自然数
- ``Language.BCoPL.DataLevel.Nat``： 自然数の加算・乗算
- ``Language.BCoPL.DataLevel.CompareNat``： 自然数の比較
- ``Language.BCoPL.DataLevel.Exp``： 算術式
- ``Language.BCoPL.DataLevel.EvalNatExp``： 算術式の評価
- ``Language.BCoPL.DataLevel.ReduceNatExp``： 算術式の簡約

使用例（出力の改行は編集でいれたもの）

```
% cd src/Language/BCoPL/
% ghci -v0 -i../.. ReduceNatExp.hs
ghci> sessionMulti'
ReduceMulti> S(Z)*S(Z)+S(Z)*S(Z) -*-> S(S(Z))
S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
  S(Z) * S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) * S(Z) by MR-One {
    S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) * S(Z) by R-PlusL {
      S(Z) * S(Z) ---> S(Z) by R-Times {
        S(Z) times S(Z) is S(Z) by T-Succ {
          Z times S(Z) is Z by T-Zero {  } ;
          S(Z) plus Z is S(Z) by P-Succ {
            Z plus Z is Z by P-Zero {  }
          }
        }
      }
    }
  } ;
  S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
    S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) by MR-One {
      S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) by R-PlusR {
        S(Z) * S(Z) ---> S(Z) by R-Times {
          S(Z) times S(Z) is S(Z) by T-Succ {
            Z times S(Z) is Z by T-Zero {  } ;
            S(Z) plus Z is S(Z) by P-Succ {
              Z plus Z is Z by P-Zero {  }
            }
          }
        }
      }
    } ;
    S(Z) + S(Z) -*-> S(S(Z)) by MR-One {
      S(Z) + S(Z) ---> S(S(Z)) by R-Plus {
        S(Z) plus S(Z) is S(S(Z)) by P-Succ {
          Z plus S(Z) is S(Z) by P-Zero {  }
        }
      }
    }
  }
}
```

## 型レベルプログラム

『判断』を型で，その『導出』を値で書く試みです．
REPLに型エラーなしにロードできれば，正しい導出であるということです．

現時点では『判断』を表す型をShowクラスのインスタンスできていません．
判断を表す式を評価したら導出木が出力されるといいのですが，それができない（残念な）システムです．
『判断』をShowクラスのインスタンスにする方法をご存知でしたら教えていただければ幸いです．

### 第1章

- Language.BCoPL.TypeLevel.Peano -- ペアノ自然数
- Language.BCoPL.TypeLevel.Nat -- 自然数の加算・乗算
- Language.BCoPL.TypeLevel.CompareNat -- 自然数の比較
- Language.BCoPL.TypeLevel.Exp -- 算術式
- Language.BCoPL.TypeLevel.EvalNatExp -- 算術式の評価
- Language.BCoPL.TypeLevel.ReduceNatExp -- 算術式の簡約

### 第2章

- Language.BCoPL.TypeLevel.MetaTheory.Nat -- 自然数の加算・乗算に関するメタ定理
- Language.BCoPL.TypeLevel.MetaTheory.CompareNat -- 自然数の比較に関するメタ定理
- Language.BCoPL.TypeLevel.MetaTheory.EvalNatExp -- 算術式の評価に関するメタ定理
- Language.BCoPL.TypeLevel.MetaTheory.ReduceNatExp -- 算術式の簡約に関するメタ定理

